-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_brownian_exponentialRelaxation
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.brownian_exponentialRelaxation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:23:47.820559+00:00
-- url     : https://prove2.me/theorems/8618d5ec-5a89-4c8a-9eaa-b38156bf2f5d
-- title:
--   §4.3.1 and §4.3.4: exponential relaxation in the Brownian model, (4.31)–(4.33), (4.57)–(4.58)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Let $\sigma_{\rm tot}\ge0$, $\Gamma_\beta=n_{\rm gas}v_\beta\sigma_{\rm tot}$ and $\eta=8m\Gamma_\beta/(3\sqrt\pi M)$. In the resulting Brownian moment model, let continuous $p(t),e(t)$ satisfy $p'=-\eta p$ and $e'=-2\eta(e-3/(2\beta))$, with right derivatives at zero. For $t\ge0$,
--   $$
--   p(t)=e^{-\eta t}p(0),\qquad e(t)=\frac3{2\beta}+\left(e(0)-\frac3{2\beta}\right)e^{-2\eta t}.
--   $$
--   Thus the squared mean scaled momentum decays by $e^{-2\eta t}$, and the mean squared scaled momentum relaxes to $3m/(2M)$ with the same factor, where $U=P/(Mv_\beta)$ and $\langle |U|^2\rangle=2e/(Mv_\beta^2)$. These are exact solutions of the limiting model, with no full-QLBE approximation estimate asserted.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 19, §4.3.1 and §4.3.4: exponential relaxation in the Brownian model, (4.31)–(4.33), (4.57)–(4.58)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.19–20,24–25, (4.31)–(4.33),(4.57)–(4.58): exact exponential
solutions of the Brownian moment model, including zero cross-section. -/
theorem brownian_exponentialRelaxation (a : GasTracerParameters) (beta sigmaTotal : ℝ)
    (hbeta : 0 < beta) (hsigma : 0 ≤ sigmaTotal)
    (p : ℝ → Momentum) (e : ℝ → ℝ)
    (hsol : BrownianMomentSolution (brownianFriction a beta sigmaTotal) beta p e) :
    ∀ t : ℝ, 0 ≤ t →
      p t = Real.exp (-brownianFriction a beta sigmaTotal * t) • p 0 ∧
      e t = 3 / (2 * beta) + (e 0 - 3 / (2 * beta)) *
        Real.exp (-2 * brownianFriction a beta sigmaTotal * t) ∧
      ‖(a.M * thermalSpeed a beta)⁻¹ • p t‖ ^ 2 =
        ‖(a.M * thermalSpeed a beta)⁻¹ • p 0‖ ^ 2 *
          Real.exp (-2 * brownianFriction a beta sigmaTotal * t) ∧
      2 * e t / (a.M * thermalSpeed a beta ^ 2) = 3 * a.m / (2 * a.M) +
        (2 * e 0 / (a.M * thermalSpeed a beta ^ 2) - 3 * a.m / (2 * a.M)) *
          Real.exp (-2 * brownianFriction a beta sigmaTotal * t) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
