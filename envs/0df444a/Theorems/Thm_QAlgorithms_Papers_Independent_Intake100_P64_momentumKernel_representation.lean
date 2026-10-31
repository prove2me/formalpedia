-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_momentumKernel_representation
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.momentumKernel_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:16:04.344202+00:00
-- url     : https://prove2.me/theorems/db2692df-7cca-4cc0-aca8-32673ed06ae7
-- title:
--   §2.2: momentum kernel representation, (2.7)–(2.8)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Write $L(k,P;Q)$ for (2.3), $r(P,P')$ for the momentum kernel, $M_{\rm in}(P,P';Q)=\int_{Q^\perp}L(k,P-Q;Q)\overline{L(k,P'-Q;Q)}\,dk$, and $M_{\rm out}(P)=\int dQ\int_{Q^\perp}|L(k,P;Q)|^2dk$. Then
--   $$
--   (\mathcal Lr)(P,P')=\int dQ\,M_{\rm in}(P,P';Q)r(P-Q,P'-Q)-\frac{M_{\rm out}(P)+M_{\rm out}(P')}{2}r(P,P').
--   $$
--   This rearranges the original double Lindblad integral; it does not construct a semigroup.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 6, §2.2: momentum kernel representation, (2.7)–(2.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.6–7, (2.7)–(2.8): kernel representation of the original double
integral on its common domain. No semigroup existence is asserted. -/
theorem momentumKernel_representation (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (P Pprime : Momentum) (h : KernelDomain d F r P Pprime) :
    collisionKernel d F r P Pprime =
      (∫ Q, quantumGain d F P Pprime Q * r (P - Q) (Pprime - Q)) -
        (((collisionLossRate d F P + collisionLossRate d F Pprime) / 2 : ℝ) : ℂ) * r P Pprime := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
