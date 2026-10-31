-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_infinitesimal_normalization
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.infinitesimal_normalization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:17:44.369238+00:00
-- url     : https://prove2.me/theorems/f6ecef50-8866-4bba-ad21-233d4bda3e6b
-- title:
--   §2.2: infinitesimal normalization, (2.12)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Let $J(P,Q)=M_{\rm in}^{\rm cl}(P+Q;Q)$ and let $g$ be a normalized momentum density with $\iint J(P,Q)g(P)dP\,dQ<\infty$. On the common finite-rate domains,
--   $$
--   M_{\rm out}(P)=\int J(P,Q)dQ,\qquad \int (Cg)(P)dP=0,\qquad \int(\mathcal Lr)(P,P)dP=0
--   $$
--   for an admissible kernel with diagonal $g$. Here $C$ is the classical collision operator. These are infinitesimal normalization identities, not global conservativity of an unbounded realization.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 7, §2.2: infinitesimal normalization, (2.12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.7, (2.12): loss-rate identity and infinitesimal normalization;
this is not a global conservativity theorem for an unbounded generator. -/
theorem infinitesimal_normalization (d : CollisionData) (F : TransverseFrames)
    (nu : MomentumLaw)
    (hplane : ∀ P, ∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P Q))
    (hloss : ∀ P, Integrable (outgoingIntensity d F P))
    (hdouble : Integrable (fun z : Momentum × Momentum =>
      transferRate d F z.1 z.2 * nu.value z.1)) :
    (∀ P, collisionLossRate d F P = ∫ Q, transferRate d F P Q) ∧
    (∫ P, classicalGenerator d F nu.value P) = 0 ∧
    (∀ r : MomentumKernel, (∀ P, r P P = (nu.value P : ℂ)) →
      (∀ P, KernelDomain d F r P P) → (∫ P, collisionKernel d F r P P) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
