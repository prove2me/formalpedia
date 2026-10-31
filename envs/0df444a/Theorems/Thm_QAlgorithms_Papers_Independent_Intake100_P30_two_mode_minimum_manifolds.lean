-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_two_mode_minimum_manifolds
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.two_mode_minimum_manifolds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:48:44.008243+00:00
-- url     : https://prove2.me/theorems/b4af1d38-ccdf-49ea-8a06-e79f722cda70
-- title:
--   IV.C: two-mode squeezed graph and minimum-error phase manifolds
-- statement:
--   For $\alpha>0$, let $G=\begin{psmallmatrix}0&1\\1&0\end{psmallmatrix}$ and $Z=i e^{-2\alpha G}=i\begin{psmallmatrix}\cosh2\alpha&-\sinh2\alpha\\-\sinh2\alpha&\cosh2\alpha\end{psmallmatrix}$. Every pair of local phases has error at least $\operatorname{sech}2\alpha$. Both signed families attain it:
--
--   $$\theta_1+\theta_2=\mp\pi/2\quad\Longrightarrow\quad Z'=i\operatorname{sech}2\alpha I\ \pm\ \tanh2\alpha G.$$
--
--   Phase differences are unrestricted. The Hessian certificate at the positive-edge representative is $2\operatorname{sech}2\alpha\tanh^2 2\alpha\begin{psmallmatrix}1&1\\1&1\end{psmallmatrix}\ge0$. These families are sufficient; an exhaustive equality-case classification is not asserted.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 14, IV.C: two-mode squeezed graph and minimum-error phase manifolds

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.14–15, (4.8)–(4.10): both signed minimum-error phase
manifolds, with arbitrary phase differences. These sufficient families are not
asserted to be an exhaustive classification modulo pi. -/
theorem two_mode_minimum_manifolds (alpha : ℝ) (hAlpha : 0 < alpha) :
    let Z := hGraph twoEdge alpha
    Z = !![Complex.I * (Real.cosh (2*alpha) : ℂ), -Complex.I * (Real.sinh (2*alpha) : ℂ);
      -Complex.I * (Real.sinh (2*alpha) : ℂ), Complex.I * (Real.cosh (2*alpha) : ℂ)] ∧
    (∀ theta : Fin 2 → ℝ, (Real.cosh (2*alpha))⁻¹ ≤ phaseError Z theta) ∧
    (∀ theta : Fin 2 → ℝ, theta 0 + theta 1 = -Real.pi / 2 →
      graphPhaseMobius Z theta = sechGraph twoEdge alpha ∧
      phaseError Z theta = (Real.cosh (2*alpha))⁻¹) ∧
    (∀ theta : Fin 2 → ℝ, theta 0 + theta 1 = Real.pi / 2 →
      graphPhaseMobius Z theta = sechGraph (-twoEdge) alpha ∧
      phaseError Z theta = (Real.cosh (2*alpha))⁻¹) ∧
    phaseHessian (sechGraph twoEdge alpha) =
      (2 * (Real.cosh (2*alpha))⁻¹ * (Real.tanh (2*alpha))^2) • (fun _ _ => 1) ∧
    (phaseHessian (sechGraph twoEdge alpha)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
