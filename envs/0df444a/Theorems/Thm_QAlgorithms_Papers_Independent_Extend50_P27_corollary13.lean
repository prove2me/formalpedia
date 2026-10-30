-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_corollary13
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.corollary13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:42:50.112352+00:00
-- url     : https://prove2.me/theorems/24e1942c-2bf9-4353-af70-70637620f696
-- title:
--   Corollary 13: maximum absolute row-sum bound
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   The norm explicitly defined in the source as a maximum absolute row sum satisfies
--
--   $$\max_
--   u\sum_\mu |(M_N^{(d)})_{
--   u\mu}|\le d^2.$$
--
--   This is the source's Eq. (43) norm, distinct from the Euclidean operator norm used for fidelity.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 12, Corollary 13: maximum absolute row-sum bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Corollary 13, using the explicit maximum absolute row sum defined on p.12. -/
theorem corollary13 {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    maxRowSum (teleportMatrix d N) ≤ (d : ℝ)^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
