-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_seminormal_triangular_basis
-- name    : QAlgorithms.Papers.Independent.Support21.P08.seminormal_triangular_basis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:23:18.149181+00:00
-- url     : https://prove2.me/theorems/49a92d77-cedd-462d-b08b-de751d3c2d72
-- title:
--   Seminormal triangularity, basis and involution
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume printed comparable-pair separation. Let $F_t$ be the interpolation product and $f_{st}=F_s a_{st}F_t$. For every cell pair, there are coefficients $b_{uv}\in K$ such that
--
--   $$f_{st}=a_{st}+\sum_{(u,v)\triangleright(s,t)}b_{uv}a_{uv}.$$
--
--   Here pair dominance is componentwise weak dominance with at least one strict inequality. The $f_{st}$ form a basis of $A$, and $(f_{st})^*=f_{ts}$. This conclusion retains all three clauses and needs no stronger separation.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 9, 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]

variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}

variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

/-- Lemma 3.3(a–c), PDF p.9. Triangularity, basis, and the exact involution.
Only the printed comparable-pair separation is imposed here. -/
theorem seminormal_triangular_basis (J : JMFamily D M)
    (hsep : separatesComparable J) :
    (∀ z : CellIndex Shape T, ∃ b : CellIndex Shape T → K,
      seminormal J z = D.basis z +
        ∑ w ∈ Finset.univ.filter (fun w => pairDominates w z), b w • D.basis w) ∧
    (∃ b : Module.Basis (CellIndex Shape T) K A, ∀ z, b z = seminormal J z) ∧
    (∀ l (s t : T l), D.star (seminormal J ⟨l, (s, t)⟩) =
      seminormal J ⟨l, (t, s)⟩) := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
