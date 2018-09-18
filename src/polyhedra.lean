import ring_theory.matrix

local infixl ` *ₘ ` : 70 := matrix.mul

variables {α : Type} {n m l : Type} [fintype n] [fintype m] [fintype l]

section matrix
def le [partial_order α] (M N : matrix n m α)  :=
∀i:n, ∀j:m, M i j ≤ N i j

instance [partial_order α] : has_le (matrix n m α) :=
{
  le := le
}

protected def matrix.le_refl [partial_order α] (A: matrix n m α) :
A ≤ A :=
begin
  assume i: n,
  assume j: m,
  refl
end

protected def matrix.le_trans [partial_order α] (a b c: matrix n m α)
  (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
begin
  assume i: n,
  assume j: m,
  have h1l: a i j ≤ b i j, from h1 i j,
  have h2l: b i j ≤ c i j, from h2 i j,
  transitivity,
  apply h1l,
  apply h2l,
end

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

def polyhedron [ordered_ring α] (A : matrix m n α) (b : matrix m unit α) :
  set (matrix n unit α) :=
{ x : matrix n unit α | A *ₘ x ≥ b }
