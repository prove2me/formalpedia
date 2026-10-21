-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_local_yjm_relations
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.local_yjm_relations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:51:56.933304+00:00
-- url     : https://prove2.me/theorems/24be86cc-3e34-4738-8377-d70e4011dc7c
-- title:
--   Unnumbered local YJM relations (3.2), (3.3)
-- statement:
--   In $\mathbb C[S_n]$, let $s_i=(i,i+1)$ for $1\leq i<n$ and $X_j=\sum_{a<j}(a,j)$ for $1\leq j\leq n$. Then
--
--   $$s_iX_j=X_js_i\quad(j\ne i,i+1),\qquad s_iX_i+1=X_{i+1}s_i.$$
--
--   The added $1$ is the algebra identity. These are the local relations underlying the degenerate affine Hecke algebra.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 14, Unnumbered local YJM relations (3.2), (3.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Equations (3.2),(3.3) (PDF pp.14–15). The +1 is the algebra identity. -/
theorem local_yjm_relations {n : ℕ} (i : Adjacent n) :
    (∀ j : Fin n, j ≠ i.val → j ≠ nextPosition i →
      adjacentElement i * yjm j = yjm j * adjacentElement i) ∧
    adjacentElement i * yjm i.val + 1 = yjm (nextPosition i) * adjacentElement i := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
