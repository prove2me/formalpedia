-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_friction_integralsAgree
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.friction_integralsAgree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:24:54.773383+00:00
-- url     : https://prove2.me/theorems/62adcedf-59c5-4569-971e-80baa30f247c
-- title:
--   §5.2.3 and Appendix A.3: microscopic friction integrals agree, (5.11)–(5.14), (A.32)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Suppose the on-shell cross-section is $\sigma(\theta;p)$, a function of the incoming magnitude and scattering angle, and all plane and angular integrals below are finite. Then
--   $$
--   \begin{aligned}
--   \eta&=\frac{\beta n_{\rm gas}}{6Mm}\int dQ\,|Q|\int_{Q^\perp}dk\,\mu_\beta(k+Q/2)|f(k-Q/2,k+Q/2)|^2\\
--   &=\frac{16\sqrt\pi}{3}\frac mM n_{\rm gas}\sqrt{\frac2{m\beta}}\int_0^\infty u^5e^{-u^2}\left[\int_0^\pi\sin\theta(1-\cos\theta)\sigma(\theta;u\sqrt{2m/\beta})d\theta\right]du.
--   \end{aligned}
--   $$
--   For constant $\sigma=\sigma_{\rm tot}/(4\pi)$, this is $\eta=8m\Gamma_\beta/(3\sqrt\pi M)$. The identity equates the microscopic coefficients without asserting a dynamical Brownian limit.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 28, §5.2.3 and Appendix A.3: microscopic friction integrals agree, (5.11)–(5.14), (A.32)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State relativeEntropy traceNormTopology)

open QAlgorithms.Papers.Independent.Next46.P09 (IsTraceLinear IsTraceCP)

/-- PDF pp.25,27–28,57, (5.11)–(5.14),(A.32): the microscopic quantum
and classical friction integrals agree, with the velocity square root retained. -/
theorem friction_integralsAgree (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta) (sigma : ℝ → ℝ → ℝ)
    (hisotropic : ∀ pf pi, pi ≠ 0 → ‖pf‖ = ‖pi‖ →
      crossSection d pf pi = sigma (Real.arccos (momentumDot pf pi / (‖pf‖ * ‖pi‖))) ‖pi‖)
    (hplane : ∀ᵐ Q : Momentum, Integrable (fun k : TransversePlane =>
      maxwell d.parameters.m beta (F.map Q k + (1 / 2 : ℝ) • Q) *
        crossSection d (F.map Q k - (1 / 2 : ℝ) • Q) (F.map Q k + (1 / 2 : ℝ) • Q)))
    (houter : Integrable (fun Q => ‖Q‖ * ∫ k : TransversePlane,
      maxwell d.parameters.m beta (F.map Q k + (1 / 2 : ℝ) • Q) *
        crossSection d (F.map Q k - (1 / 2 : ℝ) • Q) (F.map Q k + (1 / 2 : ℝ) • Q)))
    (hangular : ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      IntegrableOn (fun theta => Real.sin theta * (1 - Real.cos theta) *
        sigma theta (u * Real.sqrt (2 * d.parameters.m / beta))) (Set.Icc 0 Real.pi))
    (hu : IntegrableOn (fun u => u ^ 5 * Real.exp (-u ^ 2) *
      ∫ theta in Set.Icc (0 : ℝ) Real.pi,
        Real.sin theta * (1 - Real.cos theta) * sigma theta (u * Real.sqrt (2 * d.parameters.m / beta)))
      (Set.Ioi 0)) :
    planeFriction d F beta = angularFriction d.parameters beta sigma ∧
    (∀ sigmaTotal : ℝ, 0 ≤ sigmaTotal → (∀ theta p, sigma theta p = sigmaTotal / (4 * Real.pi)) →
      planeFriction d F beta = brownianFriction d.parameters beta sigmaTotal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
