-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_cell_irreducible
-- name    : QAlgorithms.Papers.Independent.Support21.P08.cell_irreducible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:27:33.958586+00:00
-- url     : https://prove2.me/theorems/e2571fc2-abaf-4253-b5be-857adffe1f4e
-- title:
--   Every nonempty separated cell module is irreducible
-- statement:
--   Let $K$ be a field and $A$ a unital cellular $K$-algebra with finite cell datum $(\Lambda,T,a)$, ordered tableau sets, and exact index-swapping involution. Let $L_1,\ldots,L_M$ be commuting, involution-fixed JM elements with triangular-action contents $c_t(i)$. Assume that the complete content sequences distinguish all tableaux, including tableaux of different shapes. Define $F_t$ by the interpolation product of Definition 3.1, $f_{st}=F_s a_{st}F_t$, and $\gamma_t$ as the coefficient of $a_{tt}$ in $f_{tt}^2$. For a shape $\lambda$ with $T(\lambda)\ne\varnothing$, the radical is zero and the right cell module is irreducible:
--
--   $$C(\lambda)=D(\lambda),\qquad C(\lambda)\text{ is irreducible}.$$
--
--   Irreducibility means a nonzero module whose only invariant $K$-subspaces are zero and the whole module. Nonempty cells encode the source's implicit convention excluding phantom shapes.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 13, 3.15

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

/-- Corollary 3.15, PDF p.13. Cell shapes have nonempty tableau sets, as
implicitly required when the source fixes a row. C=D means zero radical.
Uses the corrected complete content-sequence separation. -/
theorem cell_irreducible (J : JMFamily D M) (hsep : separatesAll J)
    (l : Shape) (hne : Nonempty (T l)) :
    ZeroCellRadical D l ∧ IrreducibleCell D l := by sorry

end SeparatedDefinitions

end QAlgorithms.Papers.Independent.Support21.P08

end
