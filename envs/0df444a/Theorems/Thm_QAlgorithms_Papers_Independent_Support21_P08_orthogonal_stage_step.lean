-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_orthogonal_stage_step
-- name    : QAlgorithms.Papers.Independent.Support21.P08.orthogonal_stage_step
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:33:00.869441+00:00
-- url     : https://prove2.me/theorems/3b029ca1-b63f-4a04-a599-0ef79f63255b
-- title:
--   One noncommutative orthogonalization step
-- statement:
--   Let $H$ be a unital ring and $0\le k<d$. Let $e_1,\ldots,e_k$ be pairwise orthogonal idempotents and $f_{k+1},\ldots,f_d$ directed idempotents, mutually orthogonal to all the $e_i$. Put $F=\sum_{i=1}^k e_i+f_{k+1}$. The enlarged prefix remains pairwise orthogonal, and the modified tail
--
--   $$\widehat f_j=(1-F)f_j\qquad(j\ge k+2)$$
--
--   consists of directed idempotents orthogonal to the enlarged prefix in both directions. The old tail is nonempty, while the old prefix and new tail may be empty.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 26, App.4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section RingAppendix

variable {H : Type*} [Ring H]

/-- Appendix Lemma 4.1, PDF pp.26–27. The old tail is NONEMPTY (k<d),
so its first element exists. The old prefix and new tail may be empty.
No commutativity is imposed. -/
theorem orthogonal_stage_step {d : ℕ} (f : Fin d → H) (k : ℕ)
    (hk : k < d) (hstage : OrthogonalStage f k) :
    OrthogonalStage (orthogonalStep f k) (k + 1) := by sorry

end RingAppendix

end QAlgorithms.Papers.Independent.Support21.P08

end
