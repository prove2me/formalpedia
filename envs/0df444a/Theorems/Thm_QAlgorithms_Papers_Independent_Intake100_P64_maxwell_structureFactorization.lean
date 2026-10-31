-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_maxwell_structureFactorization
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.maxwell_structureFactorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:31:09.031087+00:00
-- url     : https://prove2.me/theorems/1f2eb2e5-0cee-43ae-959a-d166e27d3f70
-- title:
--   §8.1.1: Maxwell dynamic structure factor and factorization, (8.1)–(8.3), (8.5), (8.8)–(8.9)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   For $Q\ne0$ and $E(Q,P)=|Q|^2/(2M)+Q\cdot P/M$, the Maxwell energy-shell integral, represented by Euclidean plane integration with Jacobian $m/|Q|$, equals
--   $$
--   S_{\rm MB}(Q,E)=\sqrt{\frac{\beta m}{2\pi}}\frac1{|Q|}\exp\left[-\frac{\beta(|Q|^2+2mE)^2}{8m|Q|^2}\right].
--   $$
--   With $\mu^{(2)}_\beta(k)=\beta e^{-\beta|k|^2/(2m)}/(2\pi m)$ on $Q^\perp$, one also has $(m/|Q|)\mu_\beta(k+mQ/(2m_*)+(m/M)P_{\parallel Q})=\mu^{(2)}_\beta(k)S_{\rm MB}(Q,E(Q,P))$. The function's assigned value zero at null $Q$ concerns the Lebesgue collision integral only, not a possible spectral delta contribution.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 45, §8.1.1: Maxwell dynamic structure factor and factorization, (8.1)–(8.3), (8.5), (8.8)–(8.9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.44–45, (8.5),(8.8)–(8.9): actual coarea evaluation and Maxwell
factorization, with m/|Q| as the on-shell Jacobian. -/
theorem maxwell_structureFactorization (a : GasTracerParameters) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta) (Q P : Momentum) (hQ : Q ≠ 0) :
    (a.m / ‖Q‖ * ∫ k : TransversePlane,
      maxwell a.m beta (F.map Q k +
        ((‖Q‖ ^ 2 + 2 * a.m * energyTransfer a Q P) / (2 * ‖Q‖ ^ 2)) • Q)) =
      maxwellStructure a beta Q (energyTransfer a Q P) ∧
    (∀ k : TransversePlane, a.m / ‖Q‖ * maxwell a.m beta (gasArgument a (F.map Q k) P Q) =
      maxwellPlane a.m beta (F.map Q k) * maxwellStructure a beta Q (energyTransfer a Q P)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
