-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_large_dimension
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.large_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:55:29.357233+00:00
-- url     : https://prove2.me/theorems/beee7950-9754-446c-84d9-55258f4cd0e4
-- title:
--   Eq.(100): analytic fidelity in the full-spectrum regime
-- statement:
--   For $N\ge1$ ports of local dimension $d\ge1$, let $\mathcal Y_N^{(d)}$ be the Young diagrams of $N$ boxes and height at most $d$. The physical teleportation matrix $M_N^{(d)}$ has diagonal equal to the number of removable corners and off-diagonal entry one exactly for distinct shapes related by a single-box move; all other entries vanish. Write $\lambda_{\max}$ for its largest eigenvalue and $F_{\mathrm{opt}}(N,d)$ for the maximum entanglement fidelity over the resource and Alice's measurement. Bob retains the named port and makes no unitary correction.
--
--   When $d\ge N$,
--
--   $$F_{\mathrm{opt}}(N,d)=\frac{N}{d^2}.$$
--
--   This is the full-spectrum regime. The printed condition $d\le N$ in Eq. (100) is reversed, as Corollary 8 and Section 5.3 require.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 22, Eq.(100): analytic fidelity in the full-spectrum regime

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

/-- Eq.(100), corrected full-spectrum regime d>=N (PDF p.22). Printed d<=N is
reversed, as Corollary 8, adjacent prose, and Section 5.3 require. -/
theorem large_dimension {d N : ℕ} (hN : 0 < N) (hd : N ≤ d) :
    pbtOptimalFidelity d N = (N : ℝ) / (d : ℝ)^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
