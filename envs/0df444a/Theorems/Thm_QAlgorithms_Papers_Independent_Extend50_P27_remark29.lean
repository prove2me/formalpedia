-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_remark29
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.remark29
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:52:24.592009+00:00
-- url     : https://prove2.me/theorems/bb821a3a-45b0-4a9e-b9bf-8a07059acd2a
-- title:
--   Remark 29 and Eq.(56): full-matrix maximal-eigenvalue recursion
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   The largest eigenvalues satisfy the base case and recursion
--
--   $$\lambda_{\max}(M_1)=1,\qquad
--   \lambda_{\max}(M_N)=1+\lambda_{\max}(M_{N-1})\quad(N\ge2),\qquad
--   \lambda_{\max}(M_N)=N\quad(N\ge1).$$
--
--   This states the entire maximal-eigenvalue conclusion without invoking a zero-port recursion.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 15, Remark 29 and Eq.(56): full-matrix maximal-eigenvalue recursion

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

/-- Remark 29 and Eq.(56): base case, recursion, and closed value (PDF p.15). -/
theorem remark29 :
    topValue (fullMatrix 1) = 1 ∧
    (∀ N : ℕ, 2 ≤ N → topValue (fullMatrix N) = 1 + topValue (fullMatrix (N-1))) ∧
    (∀ N : ℕ, 0 < N → topValue (fullMatrix N) = N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
