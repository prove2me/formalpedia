-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_opticalPotential_decomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.opticalPotential_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:26:53.710279+00:00
-- url     : https://prove2.me/theorems/7d7d643d-2a72-489d-9013-13915a092bda
-- title:
--   §6.2: optical-potential decomposition, (6.7)–(6.9)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Under the optical-theorem conditions at both momentum arguments and the common kernel domain, put $V_{\rm opt}(P)=-2\pi\hbar^2n_{\rm gas}F(P)/m_*$. Then
--   $$
--   \mathcal M\rho=\frac{[H_0,\rho]}{i\hbar}+\frac{V_{\rm opt}\rho-\rho V_{\rm opt}^{\dagger}}{i\hbar}+\operatorname{gain}(\rho),\qquad H_0=P^2/(2M).
--   $$
--   For a normalized measurable square-integrable wave function $\psi$, the no-jump multiplier $\psi_t(P)=e^{-it(H_0(P)+V_{\rm opt}(P))/\hbar}\psi(P)$ remains square-integrable, has squared norm in $(0,1]$, and its kernel factorizes as $\psi_t(P)\overline{\psi_t(P')}$. Thus the conditioned part preserves rank-one character while losing normalization. The gain remains in the unconditional equation; its infinitesimal trace cancellation is recorded in (2.12).
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 31, §6.2: optical-potential decomposition, (6.7)–(6.9)

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

/-- PDF p.31, (6.7)–(6.9): optical-potential decomposition on the common
domain, with complex conjugation on the right potential and gain retained. -/
theorem opticalPotential_decomposition (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (P Pprime : Momentum) (hdom : KernelDomain d F r P Pprime)
    (hP : OpticalDomain d F P) (hPprime : OpticalDomain d F Pprime) :
    fullKernel d F r P Pprime =
      (-Complex.I / d.parameters.hbar) *
        ((‖P‖ ^ 2 / (2 * d.parameters.M) - ‖Pprime‖ ^ 2 / (2 * d.parameters.M) : ℝ) : ℂ) * r P Pprime +
      (-Complex.I / d.parameters.hbar) *
        (opticalPotential d P * r P Pprime - r P Pprime * star (opticalPotential d Pprime)) +
      (∫ Q, quantumGain d F P Pprime Q * r (P - Q) (Pprime - Q)) ∧
    (∀ (psi : Momentum → ℂ) (t : ℝ), 0 ≤ t → AEStronglyMeasurable psi →
      Integrable (fun p => Complex.normSq (psi p)) →
      (∫ p, Complex.normSq (psi p)) = 1 →
      (∀ p, OpticalDomain d F p) →
      AEStronglyMeasurable (noJumpWave d psi t) ∧
      Integrable (fun p => Complex.normSq (noJumpWave d psi t p)) ∧
      0 < (∫ p, Complex.normSq (noJumpWave d psi t p)) ∧
      (∫ p, Complex.normSq (noJumpWave d psi t p)) ≤ 1 ∧
      (∀ p pprime, noJumpKernel d t (fun x y => psi x * star (psi y)) p pprime =
        noJumpWave d psi t p * star (noJumpWave d psi t pprime))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
