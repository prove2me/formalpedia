-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_refractiveIndex_diluteExpansion
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.refractiveIndex_diluteExpansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:27:25.093812+00:00
-- url     : https://prove2.me/theorems/bf280253-dd64-42fb-8d6f-c21505427ac4
-- title:
--   §6.3: refractive index, attenuation, and dilute-gas expansion, (6.10)–(6.16)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   Fix a nonzero wave vector $K$, a path length $\ell\ge0$, and optical-theorem data at beam momentum $P=\hbar K$. Let gas density $n$ vary with all other data fixed, let $E=\hbar^2|K|^2/(2M)$, and let $F=F(\hbar K)$. With the square-root branch equal to one at $n=0$,
--   $$
--   \mathfrak n(n)=\sqrt{1-V_{\rm opt}(n)/E}=1+\frac{2\pi nM}{|K|^2m_*}F+O(n^2).
--   $$
--   Explicitly there exist $C,\delta>0$, before the density variable, bounding the remainder by $Cn^2$ for $0\le n\le\delta$. The imaginary first-order term at the model density is $M_{\rm out}(P)M/(2\hbar|K|^2)$, so its attenuation exponent $2\operatorname{Im}\mathfrak n_{\rm linear}|K|\ell$ equals $M_{\rm out}(P)\ell/(|P|/M)$. The exact propagation multiplier has squared modulus $e^{-2\operatorname{Im}\mathfrak n(n)|K|\ell}$. This is conditioned forward-beam optics; the first-order parts are not exact at arbitrary density.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 32, §6.3: refractive index, attenuation, and dilute-gas expansion, (6.10)–(6.16)

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

/-- PDF pp.31–32, (6.10)–(6.16): exact square-root relation, controlled
first-order dilute-gas expansion, and attenuation of the conditioned forward
beam. Taylor constants may depend on the fixed beam and collision data. -/
theorem refractiveIndex_diluteExpansion (d : CollisionData) (F : TransverseFrames)
    (K : Momentum) (hK : K ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (hoptical : OpticalDomain d F (d.parameters.hbar • K)) :
    (∀ n : ℝ, refractiveIndex d K n ^ 2 =
      1 - (n / d.parameters.density : ℝ) * opticalPotential d (d.parameters.hbar • K) /
        (‖d.parameters.hbar • K‖ ^ 2 / (2 * d.parameters.M) : ℝ)) ∧
    (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ n : ℝ, 0 ≤ n → n ≤ delta →
      ‖refractiveIndex d K n - (1 + (n : ℂ) * refractiveSlope d K)‖ ≤ C * n ^ 2) ∧
    d.parameters.density * (refractiveSlope d K).im =
      collisionLossRate d F (d.parameters.hbar • K) * d.parameters.M /
        (2 * d.parameters.hbar * ‖K‖ ^ 2) ∧
    2 * (d.parameters.density * (refractiveSlope d K).im) * ‖K‖ * L =
      collisionLossRate d F (d.parameters.hbar • K) * L / (d.parameters.hbar * ‖K‖ / d.parameters.M) ∧
    (∀ n : ℝ, ‖Complex.exp (Complex.I * refractiveIndex d K n * (‖K‖ * L : ℝ))‖ ^ 2 =
      Real.exp (-2 * (refractiveIndex d K n).im * ‖K‖ * L)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
