-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_zero_exponent_sum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.zero_exponent_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:36:54.311495+00:00
-- url     : https://prove2.me/theorems/c4ce8796-4262-46a9-991a-8bbf308b6cb9
-- title:
--   Auxiliary alpha-zero endpoint and derivative
-- statement:
--   For each integer $n\ge1$ define $P_n(\alpha)=\sum_{\ell=1}^{n-1}(\ell/n)/\sin(\pi\ell/n)^{2\alpha}$. Then
--   $$P_n(0)=\frac{n-1}{2}.$$
--   The explicit linear continuation $P(t)=(t-1)/2$ has derivative $P'(1)=1/2$. This is an auxiliary mathematical endpoint, not a compactified theory at zero coupling or radius.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 31, Appendix D.3, unnumbered endpoint

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.31, unnumbered alpha=0 endpoint. This is an auxiliary sum,
not an assertion about a compact boson at eta=0. -/
theorem zero_exponent_sum (n : ℕ) (hn : 1 ≤ n) :
    replicaP n 0 = ((n : ℝ) - 1) / 2 ∧
    HasDerivAt zeroPContinuation (1 / 2) 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
