import ring_theory.matrix
import data.rat
import data.set data.set.enumerate data.set.finite
import set_theory.cardinal


variables {α : Type} {n m l s t : Type} [fintype n] [fintype m] [fintype s] [fintype t]

variables {n1 n2 : nat}

section matrix
def le [partial_order α] (M N : matrix n m α)  :=
∀i:n, ∀j:m, M i j ≤ N i j

instance [partial_order α] : has_le (matrix n m α) :=
{ le := le }

protected lemma matrix.le_refl [partial_order α] (A: matrix n m α) :
A ≤ A :=
by intros i j; refl

protected lemma matrix.le_trans [partial_order α] (a b c: matrix n m α)
  (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
by intros i j; transitivity; solve_by_elim

protected lemma matrix.le_antisymm [partial_order α] (a b: matrix n m α)
  (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
by ext i j; exact le_antisymm (h1 i j) (h2 i j)

instance [partial_order α] : partial_order (matrix n m α) :=
{
  le := le,
  le_refl := matrix.le_refl,
  le_trans := matrix.le_trans,
  le_antisymm := matrix.le_antisymm
}

end matrix

local infixl ` *ₘ ` : 70 := matrix.mul

def polyhedron [ordered_ring α] (A : matrix m n α) (b : matrix m unit α) :
  set (matrix n unit α) :=
{ x : matrix n unit α | A *ₘ x ≥ b }

def vec (n: Type) (α : Type) [fintype n] :=
n → α

instance [ordered_ring α] [decidable_rel ((≤) : α → α → Prop)]
  (A : matrix m n α) (b : matrix m unit α) (x : matrix n unit α) :
  decidable (x ∈ polyhedron A b) :=
show decidable (∀i:m, ∀j:unit, b i j ≤ (A *ₘ x) i j),
  by apply_instance

variables [ordered_ring α] (A B : matrix m n α) (b : matrix m unit α)

protected def matrix.row (A : matrix m n α) (row : m) : matrix unit n α :=
λ x: unit, λ y: n, (A row) y

lemma polyhedron_rowinE [ordered_ring α]
        (x: matrix n unit α) (A: matrix m n α) (b: matrix m unit α):
    x ∈ (polyhedron A b) = ∀ i:m, (matrix.row A i *ₘ x) () () ≥ b i () :=

propext $ iff.intro
  (assume h: x ∈ (polyhedron A b),
   assume d: m,
   show (matrix.row A d *ₘ x) () () ≥ b d (),
   begin
     rw polyhedron at h,
     rw set.mem_set_of_eq at h,
     exact h d ()
   end
  )
  (assume h: ∀ i:m, (matrix.row A i *ₘ x) () () ≥ b i (),
   show x ∈ (polyhedron A b),
   begin
   assume d : m,
   assume j : unit,
   rw <-(≥),
   cases j,
   apply h,
   end
  )

def active_ineq [ordered_ring α] (x: matrix n unit α)
    (A: matrix m n α) (b: matrix m unit α) : set m :=
{ i | ((A *ₘ x) i () == b i ())}

def pick_encodable (α : Type) (p : α → Prop) [decidable_pred p]:
Π (m n), matrix (fin m) (fin n) α → option(fin m × fin n)
| x y V :=
  if h : ∃ (ij : fin x × fin y), p (V ij.1 ij.2)
    then let idx := encodable.choose h in
      some idx
    else
      none 

def xrow [decidable_eq m] (row1: m) (row2: m) (A: matrix m n α) : matrix m n α :=
λ x y, if x = row1
         then
           A row2 y
         else
           if x = row2
             then 
               A row1 y
             else
               A x y

def xcol [decidable_eq n] (col1: n) (col2: n) (A: matrix m n α) : matrix m n α :=
λ x y, if y = col1
         then
           A x col2
         else
           if y = col2
             then 
               A x col1 
             else
               A x y


def fin_prefix {n} (i : fin n) (k) : fin (n + k) :=
⟨i.1, sorry ⟩

variables {m' n': Type} [fintype m'] [fintype n']

def nat_add {n} (k) (i : fin n) : fin (k + n) :=
⟨k + i.1, nat.add_lt_add_left i.2 _⟩

def minormx
  (A: matrix m n α)
  (trans_col: (m' → m))
  (trans_row: (n' → n)) :
  matrix m' n' α :=
λ i j, A (trans_col i) (trans_row j)

def rsubmx {m n_left n_right: nat}
  (A : matrix (fin m) (fin (n_left + n_right)) α) :
  matrix (fin m) (fin (n_right)) α :=
minormx A (λ i, i) (λ j, nat_add n_left j)

def lsubmx {m n_left n_right: nat}
  (A: matrix (fin m) (fin (n_left + n_right)) α):
  matrix (fin m) (fin (n_left)) α :=
minormx A (λ i, i) (λ j, fin_prefix j n_right)

def usubmx {m_down m_up n: nat}
  (A: matrix (fin (m_up + m_down)) (fin n) α) :
  matrix (fin m_up) (fin n) α :=
minormx A (λ i, fin_prefix i m_down) (λ j, j)

def dsubmx {m_down m_up n: nat}
  (A: matrix (fin (m_up + m_down)) (fin n) α) :
  matrix (fin m_down) (fin n) α :=
minormx A (λ i, nat_add m_up i) (λ j, j)

def ursubmx {m_down m_up n_left n_right: nat}
  (A: matrix (fin (m_up + m_down)) (fin (n_left + n_right)) α) :
  matrix (fin m_up) (fin (n_right)) α :=
usubmx (rsubmx A)

def drsubmx {m_down m_up n_left n_right: nat}
  (A: matrix (fin (m_up + m_down)) (fin (n_left + n_right)) α) :
  matrix (fin m_down) (fin (n_right)) α :=
dsubmx (rsubmx A)

def ulsubmx {m_down m_up n_left n_right: nat}
  (A: matrix (fin (m_up + m_down)) (fin (n_left + n_right)) α) :
  matrix (fin m_up) (fin (n_left)) α :=
usubmx (lsubmx A)

def dlsubmx {m_down m_up n_left n_right: nat}
  (A: matrix (fin (m_up + m_down)) (fin (n_left + n_right)) α) :
  matrix (fin m_down) (fin (n_left)) α :=
dsubmx (lsubmx A)

def fin_swap_add {x x': nat}  (F: fin (x + x')) : fin (x' + x) :=
let d := F.1 in -- I seem to need this temporary assignment for the types to work out
⟨d, begin rw nat.add_comm, apply F.2 end⟩ 

def fin_swap {m m' n n' : nat} 
  (A: matrix (fin (m + m')) (fin (n + n')) α) :
   matrix (fin (m' + m)) (fin (n' + n)) α :=
minormx A fin_swap_add fin_swap_add

def fin_first {n m} (i : fin (n + m)) {h: i.val < n}: fin (n) :=
⟨i.1, begin apply h end⟩

def fin_second {n m} (i : fin (n + m)) {h: i.val > n}: fin (m) :=
⟨i.1 - n, begin i  end⟩

#check fin_first 

def block_mx {m_down m_up n_left n_right: nat} :
  matrix (fin m_up) (fin n_left) α →
  matrix (fin m_up) (fin n_right) α →
  matrix (fin m_down) (fin n_left) α →
  matrix (fin m_down) (fin n_right) α →
  matrix (fin (m_up + m_down)) (fin (n_left + n_right)) α
| up_left up_right down_left down_right := 
λ i j,
 if i.val < m_up
 then 
   let x := j.val < n_left in
    if x
    then
      up_left (fin_first i) (fin_first j)
    else
      up_right (fin_first i) (fin_second j)
  else
   if j.val < n_left
    then
      down_left (fin_second i)  (fin_first j)
    else
      down_right (fin_second i) (fin_second j)
 
def Gaussian_elimination [decidable_eq α] [has_inv α]:
   Π (m n), matrix (fin m) (fin n) α → 
   (matrix (fin m) (fin m) α × matrix (fin n) (fin n) α × nat)
| (x+1) (y+1) A :=
  let optional_ij := pick_encodable (α) (λ el, le ≠ 0) (x+1) (y+1) A in
  match optional_ij with
  | some ij :=
    let i := ij.1 in
    let j := ij.2 in
    let a := A i j in
    let A1 := xrow i 0 (xcol j 0 A) in
    let A1' := fin_swap A1 in 
    let B := A1' in 
    let u := ursubmx A1' in 
    let v := a⁻¹ • dlsubmx A1' in
    let (L, U, r) := Gaussian_elimination (x) (y) (drsubmx A1' - (v *ₘ u)) in 
    (
      xrow i 0 (fin_swap (block_mx 1 0 v L)),
      xcol j 0 (fin_swap (block_mx (λ i1 j1, a) u 0 U)),
      r + 1
     )
  | none :=
     (
      (1 : (matrix (fin (x+1)) (fin (x+1)) α)),
      (1 : (matrix (fin (y+1)) (fin (y+1)) α)),
      0
     )
  end
| x y A :=
     (
      (1 : (matrix (fin (x)) (fin (x)) α)),
      (1 : (matrix (fin (y)) (fin (y)) α)),
      0
     )

def test : matrix (fin 3) (fin 3) rat :=
λ x y,
if (x = 0 ∧ y = 0) then 3 else
if (x = 0 ∧ y = 1) then 3 else
if (x = 0 ∧ y = 2) then 3 else
if (x = 1 ∧ y = 0) then 3 else
if (x = 1 ∧ y = 1) then 2 else
if (x = 1 ∧ y = 2) then 3 else
if (x = 2 ∧ y = 0) then 2 else
if (x = 2 ∧ y = 1) then 1 else
if (x = 2 ∧ y = 2) then 1 else
0

def getL : matrix (fin 3) (fin 3) rat :=
  let res := Gaussian_elimination 3 3 test in
  res.1

def getU : matrix (fin 3) (fin 3) rat :=
  let res := Gaussian_elimination 3 3 test in
  res.2.1

def getRank : nat :=
let res := Gaussian_elimination 3 3 test in
res.2.2

#eval (getL *ₘ getU) 2 1