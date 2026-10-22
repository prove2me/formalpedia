-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_simpleUpperBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.simpleUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:22:01.468303+00:00
-- url     : https://prove2.me/theorems/ee9e60d0-e091-4156-8956-dfd7f84adb43
-- title:
--   §II, unnumbered logarithmic upper bound (5)
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. For states $\rho,\sigma$ with $\beta=\lambda_{\min}(\sigma)>0$, let $H(\rho)=-\operatorname{Tr}(\rho\log\rho)$. Then
--
--   $$
--   D(\rho\|\sigma)\le-H(\rho)-\log\beta\le-\log\beta.
--   $$
--
--   Both preliminary upper inequalities are retained.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 2, §II, unnumbered logarithmic upper bound (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.2, Eq.(5): both preliminary logarithmic upper inequalities. -/
theorem simpleUpperBound {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    relativeEntropy rho sigma ≤ ((-entropy rho - Real.log (minEigenvalue sigma) : ℝ) : EReal) ∧
    -entropy rho - Real.log (minEigenvalue sigma) ≤ -Real.log (minEigenvalue sigma) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
