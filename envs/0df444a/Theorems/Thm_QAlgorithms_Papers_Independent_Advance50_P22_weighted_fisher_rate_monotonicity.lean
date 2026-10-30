-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_weighted_fisher_rate_monotonicity
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.weighted_fisher_rate_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:11:31.318272+00:00
-- url     : https://prove2.me/theorems/c638faa3-510e-41e6-952a-5e87ff4bec61
-- title:
--   Section III B, Eq.(29): weighted Fisher bound and monotonicity of the rate
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian scattering channel, and let its independent normalized inputs have finite mean photon number. Write $\lambda_\alpha=|\det M_\alpha|^{1/n}$ and define $\gamma_\alpha$ by the nonsingular inverse formula, with zero noise otherwise. At arbitrary nonnegative local times, wherever the active input Fisher Hessians and the output Hessian are defined on their finite twice-differentiability domains,
--
--   $$\left(\sum_\alpha\lambda_\alpha e^{S_\alpha/n}\right)^2\operatorname{tr}J_Y\le\sum_{\alpha:\det M_\alpha\ne0}\lambda_\alpha e^{2S_\alpha/n}\operatorname{tr}(J_\alpha\gamma_\alpha).$$
--
--   For any clocks solving the entropy clock equations, the rate $R(\tau)=\bigl(\sum_\alpha\lambda_\alpha e^{S_\alpha(\tau)/n}\bigr)e^{-S_Y(\tau)/n}$ is nondecreasing on $[0,\infty)$ and differentiable with $R'(\tau)\ge0$ for $\tau>0$. Singular blocks have no Fisher evaluation, and zero rate is allowed. This is the nonnegative derivative statement used in the proof.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 4, Section III B, Eq.(29): weighted Fisher bound and monotonicity of the rate

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov PhysicalCovariance FiniteMeanEnergy
   productWeyl weylArgument multimodeWeylTrace)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Next46.P17
  (bosonicEntropyPower conjugateCoefficient firstMoments quadratureCovariance
   gaussianCoefficient gaussification)

open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)

/-- PDF pp.3--4, Section III B, (29): lambda (not lambda squared) on the
right; singular inputs are omitted before evaluating their Hessians or inverses.
Printed 'positivity' means nonnegativity: identical thermal inputs give equality.
Both monotonicity and the nonnegative derivative of the finite-entropy rate are
conclusions for the constructed clocks, including constant zero rate.
-/
theorem weighted_fisher_rate_monotonicity {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n))
    (hEnergy : ∀ a, FiniteMeanEnergy (rho a).coefficients)
    (clock : Fin K → ℝ → ℝ)
    (hclock : EntropyClocks C.block (fun a => (rho a).coefficients) clock) :
    (let X := evolvedInputs C.block (fun a => (rho a).coefficients)
     ∀ times : Fin K → ℝ, (∀ a, 0 ≤ times a) →
       (∀ a, (C.block a).det ≠ 0 → MatrixFisherRegular (X times a)) →
       MatrixFisherRegular (C.channel (independentInput (X times))) →
       (∑ a, determinantWeight (C.block a) *
         Real.exp ((extendedEntropyNats (X times a)).toReal / (n : ℝ))) ^ 2 *
           (matrixFisher (C.channel (independentInput (X times)))).trace ≤
       ∑ a ∈ Finset.univ.filter (fun a => (C.block a).det ≠ 0),
         determinantWeight (C.block a) *
           Real.exp (2 * (extendedEntropyNats (X times a)).toReal / (n : ℝ)) *
             (matrixFisher (X times a) * inputNoise (C.block a)).trace) ∧
    (let R := fun tau => scatteringEntropyPowerRatio C (fun a => (rho a).coefficients) (fun a => clock a tau)
     MonotoneOn R (Set.Ici 0) ∧
       ∀ tau : ℝ, 0 < tau → DifferentiableAt ℝ R tau ∧ 0 ≤ deriv R tau) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
