-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_optical_forwardLoss
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.optical_forwardLoss
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:26:15.078616+00:00
-- url     : https://prove2.me/theorems/a1950011-4cd6-4e5b-951d-0b9c4b028e54
-- title:
--   §6.1–6.2: forward amplitude gives the shift and collision loss, (6.1)–(6.6)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Let $F(P)=\int\mu(p)f(\operatorname{rel}(p,P),\operatorname{rel}(p,P))dp$, and let $\sigma_{\rm tot}(p)=\int d\Omega\,\sigma(|p|n,p)$. Assume the physical optical theorem $\sigma_{\rm tot}(p)=4\pi\hbar\operatorname{Im}f(p,p)/|p|$ for $p\ne0$ and finite forward/flux/plane integrals. Then
--   $$
--   M_{\rm out}(P)=\frac{n_{\rm gas}}{m_*}\int\mu(p)|\operatorname{rel}(p,P)|\sigma_{\rm tot}(\operatorname{rel}(p,P))dp
--   =\frac{4\pi\hbar n_{\rm gas}}{m_*}\operatorname{Im}F(P).
--   $$
--   The gas shift equals $\operatorname{Re}V_{\rm opt}(P)$, where $V_{\rm opt}=-2\pi\hbar^2n_{\rm gas}F/m_*$. A real first Born amplitude cannot replace the physical optical-theorem data in this assertion.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 31, §6.1–6.2: forward amplitude gives the shift and collision loss, (6.1)–(6.6)

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

/-- PDF pp.30–31, (6.1)–(6.6): optical theorem gives both the microscopic
loss rate and the forward energy shift. An arbitrary complex amplitude without
the optical theorem is not enough for this conclusion. -/
theorem optical_forwardLoss (d : CollisionData) (F : TransverseFrames)
    (P : Momentum) (h : OpticalDomain d F P) :
    collisionLossRate d F P = fluxLoss d P ∧
    collisionLossRate d F P = 4 * Real.pi * d.parameters.hbar * d.parameters.density /
      reducedMass d.parameters * (forwardAverage d P).im ∧
    energyShift d P = (opticalPotential d P).re := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
