-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_boost_collisionAndShift
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.boost_collisionAndShift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:21:16.311091+00:00
-- url     : https://prove2.me/theorems/37e4e36a-cec6-4a8b-b755-12cb28915b77
-- title:
--   §4.1.2: collision coefficient and energy shift under boosts, (4.4)–(4.5)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a fixed velocity $v$, set $\mu^v(p)=\mu(p-mv)$. With subscripts indicating the gas law used,
--   $$
--   L_\mu(p,P-Mv;Q)=L_{\mu^v}(p+mv_{\perp Q},P;Q),\qquad H_{n,\mu}(P-Mv)=H_{n,\mu^v}(P).
--   $$
--   Conjugating the collision kernel by the momentum boost equals evaluating it with $\mu^v$, on their common domain. This conclusion concerns the collision term and gas shift; the source's separate full-generator boost assertion is deferred.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 15, §4.1.2: collision coefficient and energy shift under boosts, (4.4)–(4.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.15, (4.4)–(4.5): collision coefficient and gas shift under boosts;
the erroneous assertion about the free Hamiltonian is excluded. -/
theorem boost_collisionAndShift (d : CollisionData) (F : TransverseFrames)
    (v P : Momentum)
    (hforward : Integrable (fun p => (d.gas.value p : ℂ) *
      d.amplitude (relativeMomentum d.parameters p (P - d.parameters.M • v))
        (relativeMomentum d.parameters p (P - d.parameters.M • v)))) :
    (∀ p Q, collisionCoefficient d p (P - d.parameters.M • v) Q =
      boostedCoefficient d v (p + d.parameters.m • perpendicular v Q) P Q) ∧
    energyShift d (P - d.parameters.M • v) = boostedEnergyShift d v P ∧
    (∀ (r : MomentumKernel) (Pprime : Momentum),
      KernelDomain d F
        (fun A B => r (A + d.parameters.M • v) (B + d.parameters.M • v))
        (P - d.parameters.M • v) (Pprime - d.parameters.M • v) →
      collisionKernel d F
        (fun A B => r (A + d.parameters.M • v) (B + d.parameters.M • v))
        (P - d.parameters.M • v) (Pprime - d.parameters.M • v) =
          boostedCollisionKernel d F v r P Pprime) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
