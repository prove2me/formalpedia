-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_half_cross_ratio_continuation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.half_cross_ratio_continuation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:34:17.091364+00:00
-- url     : https://prove2.me/theorems/9e474513-87bc-4d82-aeb8-ba9b218e8f7c
-- title:
--   Explicit half-cross-ratio continuation and negative derivative
-- statement:
--   For $n>0$ define
--   $$h_n(t)=\frac{e^{-t}}t\left(\frac{e^t(e^{t/2}-1-n(e^{t/(2n)}-1))}{(e^t-1)(e^{t/(2n)}-1)}+\frac{1-n}{4}\right),\quad D(n)=\frac{n-1}{2}\log\pi-2\int_0^\infty h_n(t)\,dt.$$
--   The combined integrand is integrable. At each positive integer $n$, $D(n)=\sum_{k=1}^{n-1}\log{}_2F_1(k/n,1-k/n;1;1/2)$. If $j(t)=\frac{e^{-t}}{2t}\frac{e^{3t/2}(2t-5)+5e^t+e^{t/2}-1}{(e^t-1)(e^{t/2}-1)}$, then $j$ is integrable and
--   $$-D'(1)=-\tfrac12\log\pi+\int_0^\infty j(t)\,dt=\tfrac12(-1-\gamma_E+\log\pi).$$
--   The derivative exists, and its negative is the source's $D'_1(1/2)$. This concrete continuation needs no general replica-continuation uniqueness assertion; logarithms are natural.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 30, Appendix D.1, Eqs. (D.5)–(D.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source pp.29--30, (D.5)--(D.7): a concrete positive-real-n continuation
at x=1/2, its agreement with integer data, and its negative derivative.
The source defines D1prime as MINUS the derivative in (78). -/
theorem half_cross_ratio_continuation :
    (∀ n : ℝ, 0 < n → IntegrableOn (halfDIntegrand n) (Ioi 0)) ∧
    (∀ n : ℕ, 1 ≤ n → halfDContinuation (n : ℝ) =
      ∑ k : Fin (n - 1), Real.log
        (hypergeometricF (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) (1 / 2))) ∧
    HasDerivAt halfDContinuation ((1 + Real.eulerMascheroniConstant - Real.log Real.pi) / 2) 1 ∧
    IntegrableOn halfDNegativeIntegrand (Ioi 0) ∧
    -deriv halfDContinuation 1 =
      -Real.log Real.pi / 2 + ∫ t in Ioi (0 : ℝ), halfDNegativeIntegrand t ∧
    -deriv halfDContinuation 1 =
      (-1 - Real.eulerMascheroniConstant + Real.log Real.pi) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
