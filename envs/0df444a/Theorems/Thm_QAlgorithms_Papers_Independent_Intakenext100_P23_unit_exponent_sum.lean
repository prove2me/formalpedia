-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_unit_exponent_sum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.unit_exponent_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:35:31.353622+00:00
-- url     : https://prove2.me/theorems/f3db886a-cbbd-4c59-a13f-203e61ce6adb
-- title:
--   Alpha-one trigonometric sum and polynomial derivative
-- statement:
--   For every integer $n\ge1$, let $P_n(\alpha)=\sum_{\ell=1}^{n-1}(\ell/n)/\sin(\pi\ell/n)^{2\alpha}$, using an empty sum at $n=1$. Then
--   $$P_n(1)=\frac{n^2-1}{6}.$$
--   The explicit polynomial continuation $P(t)=(t^2-1)/6$ has derivative $P'(1)=1/3$. This auxiliary derivative is not a physical self-dual entropy correction, where the full quotient cancels exactly.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 31, Appendix D.3, Eq. (D.9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.31, Eq.(D.9): the alpha=1 trigonometric sum, including the
empty n=1 case, and the derivative of its explicit polynomial continuation. -/
theorem unit_exponent_sum (n : ℕ) (hn : 1 ≤ n) :
    replicaP n 1 = ((n : ℝ) ^ 2 - 1) / 6 ∧
    HasDerivAt unitPContinuation (1 / 3) 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
