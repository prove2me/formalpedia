-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P08_split_algebra_has_jm
-- name    : QAlgorithms.Papers.Independent.Support21.P08.split_algebra_has_jm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:22:31.127081+00:00
-- url     : https://prove2.me/theorems/68cb25cd-f8db-49da-8778-737909cda8c6
-- title:
--   Every split semisimple algebra admits separated JM data
-- statement:
--   Let $K$ be a field and let $A$ be a unital $K$-algebra equipped with a Wedderburn isomorphism $A\cong\prod_{j=1}^r\operatorname{Mat}_{d_j}(K)$, where all $d_j>0$. There exist a cellular datum on $A$, with $T(j)=\{1,\ldots,d_j\}$, and a family of $M$ JM elements separating all tableaux, where
--
--   $$M=\sum_{j=1}^r d_j.$$
--
--   The cellular datum is chosen as part of the conclusion; the theorem makes no claim about an arbitrary preassigned basis.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, PDF p. 5, 2.13

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section WedderburnExample

/-- Example 2.13, PDF pp.5–6. The cellular datum is chosen existentially
from the given Wedderburn decomposition. There are exactly sum_i d_i JM
operators. This makes no assertion about every prechosen cell basis. -/
theorem split_algebra_has_jm {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 0 < d i)
    (e : A ≃ₐ[K] ∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K) :
    ∃ D : CellDatum (R := K) (A := A) (T := fun i : Fin r => Fin (d i)),
      ∃ J : JMFamily D (∑ i, d i), separatesAll J := by sorry

end WedderburnExample

end QAlgorithms.Papers.Independent.Support21.P08

end
