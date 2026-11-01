-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_completeSecondMomentCriterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.completeSecondMomentCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:33:36.2277+00:00
-- url     : https://prove2.me/theorems/5cff57fa-0aa1-4a38-9601-dcbd2cf439b5
-- title:
--   Equivalent second-moment Peres–Horodecki tests
-- statement:
--   Let $\rho$ be any normalized two-mode oscillator density with finite first and second moments, mean $d$, and real symmetric covariance $V$ in interleaved coordinates, using $\hbar=1$ and vacuum $I_4/2$. Write $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$, $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, $\Omega=J\oplus J$, and $\Lambda=\operatorname{diag}(1,1,1,-1)$. Set $Q_V(x)=x^TVx$ and $a_j(x,y)=x_{q_j}y_{p_j}-x_{p_j}y_{q_j}$. Define $\mathcal S(V)$ to be the displayed scalar inequality below. The physical uncertainty condition $V+i\Omega/2\succeq0$ holds, and
--
--   $$
--   \begin{aligned}
--   \Lambda V\Lambda+i\Omega/2\succeq0
--   &\Longleftrightarrow V+i\Lambda\Omega\Lambda/2\succeq0\\
--   &\Longleftrightarrow \forall x,y\in\mathbb R^4,\ Q_V(x)+Q_V(y)\ge|a_1(x,y)|+|a_2(x,y)|\\
--   &\Longleftrightarrow \mathcal S(V):\quad
--   \det A\det B+(1/4-|\det C|)^2-\operatorname{tr}(AJCJBJC^TJ)\ge(\det A+\det B)/4.
--   \end{aligned}
--   $$
--
--   If $\rho$ is separable in trace norm, all these equivalent conditions hold. They describe the complete second-moment consequence of the partial-transpose test; Gaussianity is not assumed and non-Gaussian sufficiency for separability is not asserted.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, Equations (9)–(11), (19): complete second-moment consequence of separability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P92

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsSeparable IsBarycenter)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Advance50.P48
  (TwoKernel GaussianTwo IsDiscordCovariance characteristicTwo
   covarianceModeBlock totalPhotonEnergy)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase Covariance twoModeStandard)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

open QAlgorithms.Papers.Independent.Gap48.P47 (localSymplecticMatrix)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel unitaryCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--4, (9)--(11),(19): all second-moment forms are equivalent on
actual physical densities, and every separable finite-moment state satisfies them.
No Gaussianity or non-Gaussian sufficiency for separability is asserted. -/
theorem completeSecondMomentCriterion (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2)
    (hmom : TwoModeMoments rho d V) :
    IsDiscordCovariance V ∧
    (IsDiscordCovariance (reflectedCovariance V) ↔ ReflectedUncertainty V) ∧
    (IsDiscordCovariance (reflectedCovariance V) ↔ SeparableVarianceBound V) ∧
    (IsDiscordCovariance (reflectedCovariance V) ↔ SimonCriterion V) ∧
    (IsSeparable rho →
      IsDiscordCovariance (reflectedCovariance V) ∧ ReflectedUncertainty V ∧
        SeparableVarianceBound V ∧ SimonCriterion V) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
