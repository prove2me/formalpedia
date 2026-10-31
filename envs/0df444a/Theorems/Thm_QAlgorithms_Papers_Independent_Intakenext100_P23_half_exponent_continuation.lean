-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_half_exponent_continuation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.half_exponent_continuation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:36:19.939992+00:00
-- url     : https://prove2.me/theorems/77f8937c-dc60-4a28-bb13-9e28bdff0895
-- title:
--   Alpha-one-half integral continuation and derivative
-- statement:
--   For real $n>0$ define
--   $$P_{1/2}(n)=\frac n\pi\int_0^\infty\bigl(\coth t\tanh(nt)-1\bigr)\,dt.$$
--   The combined integrand is integrable, and at every positive integer $n$ this equals $\sum_{\ell=1}^{n-1}(\ell/n)/\sin(\pi\ell/n)$. The derivative at one exists and
--   $$P_{1/2}'(1)=\frac1\pi\int_0^\infty\frac{t}{\sinh t\cosh t}\,dt=\frac\pi8,$$
--   with an integrable derivative integrand. This provides an explicit special continuation including $P_{1/2}(1)=0$, without dividing by $n-1$ at one.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 31, Appendix D.3, Eqs. (D.12)–(D.13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.31, (D.12)--(D.13): integrable positive-real-n function for
alpha=1/2, agreement at positive integers, and the derivative pi/8 at one.
No quotient by n-1 is evaluated at n=1. -/
theorem half_exponent_continuation :
    (∀ n : ℝ, 0 < n → IntegrableOn (halfPIntegrand n) (Ioi 0)) ∧
    (∀ n : ℕ, 1 ≤ n → halfPContinuation (n : ℝ) = replicaP n (1 / 2)) ∧
    HasDerivAt halfPContinuation (Real.pi / 8) 1 ∧
    IntegrableOn halfPDerivativeIntegrand (Ioi 0) ∧
    (1 / Real.pi) * (∫ t in Ioi (0 : ℝ), halfPDerivativeIntegrand t) =
      Real.pi / 8 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
