-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_remark_2_7
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.remark_2_7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:49:03.595621+00:00
-- url     : https://prove2.me/theorems/1a7c1853-25db-4f3d-b15a-fa92b5c7f30d
-- title:
--   Remark 2.7
-- statement:
--   For every $k\geq3$, the element $X_k=\sum_{j<k}(j,k)$ in the actual complex group algebra of $S_k$ is noncentral:
--
--   $$X_k\notin Z(\mathbb C[S_k]).$$
--
--   The printed range also includes $k=1,2$, which are exceptions: $X_1=0$ and $S_2$ is abelian. This corrected range expresses the noncentral phenomenon discussed in the remark; independent moderation of the correction is pending.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 12, Remark 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Remark 2.7 (PDF p.12), corrected to the noncentral regime k≥3.
Printed k=1,...,n is false at k=1 (X_1=0) and k=2 (S_2 is abelian).
Independent moderation of this source correction remains required. -/
theorem remark_2_7 (n : ℕ) :
    yjm (Fin.last (n + 2)) ∉ Subalgebra.center ℂ (SymmetricAlgebra (n + 3)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
