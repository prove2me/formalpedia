-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_entropy_clocks_exist
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.entropy_clocks_exist
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:07:56.576794+00:00
-- url     : https://prove2.me/theorems/7cd533fc-7782-48a7-bb5a-64ea6ddfd44e
-- title:
--   Section III A, Eqs.(15)–(16): entropy-parametrized clocks
-- statement:
--   Let $n,K\ge1$, let $M_\alpha$ be the blocks of a Gaussian scattering channel, and let its independent normalized inputs have finite mean photon number. Set $\lambda_\alpha=|\det M_\alpha|^{1/n}$ and $\gamma_\alpha=\lambda_\alpha M_\alpha^{-1}M_\alpha^{-T}$ for nonsingular blocks, and $\gamma_\alpha=0$ otherwise. There exist global nonnegative clocks $t_\alpha(\tau)$, $\tau\ge0$, with
--
--   $$t_\alpha(0)=0,\qquad t_\alpha'(\tau)=\exp\!\left(\frac{S(H_{\gamma_\alpha}(t_\alpha(\tau))\rho_\alpha)}{n}\right),\qquad t_\alpha(\tau)\ge\tau,\qquad\lim_{\tau\to\infty}t_\alpha(\tau)=+\infty.$$
--
--   The derivative at zero is a right derivative. The existence assertion concerns the actual entropy functions of the heat flow and provides the parametrization used in the proof.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 3, Section III A, Eqs.(15)–(16): entropy-parametrized clocks

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

/-- PDF p.3, Section III A, (15)--(16): existence of global entropy clocks for
the actual finite-moment entropy functions, with initial condition and divergence. -/
theorem entropy_clocks_exist {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n))
    (hEnergy : ∀ a, FiniteMeanEnergy (rho a).coefficients) :
    ∃ clock : Fin K → ℝ → ℝ,
      EntropyClocks C.block (fun a => (rho a).coefficients) clock ∧
      ∀ a, (∀ tau : ℝ, 0 ≤ tau → tau ≤ clock a tau) ∧
        Tendsto (clock a) atTop atTop := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
