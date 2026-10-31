-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_quantum_structureRepresentation
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.quantum_structureRepresentation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:32:31.55132+00:00
-- url     : https://prove2.me/theorems/317232be-5ff5-48c7-a478-b98d81f1d1e6
-- title:
--   §8.1.2: exact Maxwell structure-factor form of the quantum generator, (8.10)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Write $u=\operatorname{rel}(p_{\perp Q},P_{\perp Q})$ and $S(Q,P)=S_{\rm MB}(Q,E(Q,P))$. The original coefficient equals
--   $$
--   L(p,P;Q)=\sqrt{\frac{n_{\rm gas}}{m_*^2}\mu^{(2)}_\beta(p_{\perp Q})}\,f(u-Q/2,u+Q/2)\sqrt{S(Q,P)}.
--   $$
--   Consequently the original double collision integral equals the structure-factor Lindblad expression (8.10) on the common integrable kernel domain. The momentum-dependent complex amplitude is retained, with its transverse dependence unchanged by a $Q$ shift. This does not construct a closed conservative QDS.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 46, §8.1.2: exact Maxwell structure-factor form of the quantum generator, (8.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.45–46, (8.10): exact quantum structure-factor form; complex
amplitude products are retained rather than replaced by averaged cross-sections. -/
theorem quantum_structureRepresentation (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (r : MomentumKernel) (P Pprime : Momentum) (hdom : KernelDomain d F r P Pprime) :
    (∀ p P0 Q, collisionCoefficient d p P0 Q = structureCoefficient d beta p P0 Q) ∧
    collisionKernel d F r P Pprime = structureQuantumKernel d F beta r P Pprime := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
