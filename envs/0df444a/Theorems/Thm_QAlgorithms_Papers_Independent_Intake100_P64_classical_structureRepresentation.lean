-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_classical_structureRepresentation
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.classical_structureRepresentation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:31:48.208121+00:00
-- url     : https://prove2.me/theorems/1c189919-741c-4cb9-9eca-8099e0713c7c
-- title:
--   §8.1.1: structure-factor representation of the classical equation, (8.4), (8.6)–(8.7)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Let $\sigma_{\rm av}(P,Q)=\int_{Q^\perp}\mu^{(2)}_\beta(k)\sigma(\operatorname{rel}(k,P_{\perp Q})-Q/2,\operatorname{rel}(k,P_{\perp Q})+Q/2)dk$. For an admissible profile $g$,
--   $$
--   Cg(P)=\frac{n_{\rm gas}}{m_*^2}\int dQ\,\sigma_{\rm av}(P,Q)\big[S_{\rm MB}(Q,E(Q,P-Q))g(P-Q)-S_{\rm MB}(Q,E(Q,P))g(P)\big].
--   $$
--   If $\sigma(p_f,p_i)=s(p_f-p_i)$, then $\sigma_{\rm av}(P,Q)=s(-Q)$. This uses the invariance of $P_{\perp Q}$ under the gain shift before factoring the averaged cross-section.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 45, §8.1.1: structure-factor representation of the classical equation, (8.4), (8.6)–(8.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.44–45, (8.4),(8.6)–(8.7): equivalent forms of the classical
collision equation, using invariance of perpendicular P under P -> P-Q. -/
theorem classical_structureRepresentation (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (nu : Momentum → ℝ) (P : Momentum)
    (hplane : ∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P Q) ∧
      Integrable (rateIntegrand d F (P - Q) Q))
    (hgain : Integrable (fun Q => transferRate d F (P - Q) Q * nu (P - Q)))
    (hloss : Integrable (outgoingIntensity d F P)) :
    classicalGenerator d F nu P = structureGenerator d F beta
      (fun Q p => maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q p)) nu P ∧
    (∀ sigma : Momentum → ℝ,
      (∀ pf pi, crossSection d pf pi = sigma (pf - pi)) →
      ∀ Q, averagedCrossSection d F beta P Q = sigma (-Q)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
