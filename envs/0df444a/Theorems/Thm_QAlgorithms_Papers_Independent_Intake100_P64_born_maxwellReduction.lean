-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_born_maxwellReduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.born_maxwellReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:19:20.147257+00:00
-- url     : https://prove2.me/theorems/965fdf7d-141c-42c5-a050-9f85828606d2
-- title:
--   §2.3: Maxwell–Born reduction to a single Q integral, (2.17)–(2.18)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   For real integrable $V$, replace $f$ by its Born amplitude and set $\sigma_B(Q)=|f_B(Q)|^2$. Define the nonnegative multiplier, with value zero at $Q=0$, by
--   $$
--   L_B(P;Q)=\left[\sqrt{\frac{\beta m}{2\pi}}\frac{n_{\rm gas}\sigma_B(Q)}{m_*^2|Q|}\right]^{1/2}
--   \exp\left[-\frac{\beta((1+m/M)|Q|^2+2(m/M)P\cdot Q)^2}{16m|Q|^2}\right].
--   $$
--   The double-integral collision kernel equals the single-$Q$ Lindblad kernel built from $L_B$. Moreover $H_n(P)=-2\pi\hbar^2n_{\rm gas}\operatorname{Re}f_B(0)/m_*$ is constant. This is a coefficient/generator identity on the common domain, not a QDS construction.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 8, §2.3: Maxwell–Born reduction to a single Q integral, (2.17)–(2.18)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.8, (2.17)–(2.18): exact Maxwell–Born single-Q reduction and constant
Born energy shift. No full QDS realization follows from this identity. -/
theorem born_maxwellReduction (d : CollisionData) (F : TransverseFrames)
    (V : Momentum → ℝ) (beta : ℝ) (hbeta : 0 < beta) (hV : Integrable V)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (hf : ∀ pf pi, d.amplitude pf pi = bornMatrixAmplitude d.parameters V pf pi)
    (r : MomentumKernel) (P Pprime : Momentum) (hdom : KernelDomain d F r P Pprime) :
    collisionKernel d F r P Pprime = bornKernel d.parameters beta V r P Pprime ∧
    (∀ P0, energyShift d P0 =
      -2 * Real.pi * d.parameters.hbar ^ 2 * d.parameters.density /
        reducedMass d.parameters * (bornAmplitude d.parameters V 0).re) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
