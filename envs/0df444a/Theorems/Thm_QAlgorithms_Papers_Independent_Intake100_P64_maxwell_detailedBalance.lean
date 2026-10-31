-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_maxwell_detailedBalance
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.maxwell_detailedBalance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:22:08.134017+00:00
-- url     : https://prove2.me/theorems/33b25b2b-47c9-4650-88cb-f9078abe253b
-- title:
--   §4.2.1: detailed balance and the stationary momentum profile, (4.7)–(4.13)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Assume reciprocal scattering, $\sigma(p_f,p_i)=\sigma(p_i,p_f)$, and finite plane rates. For $E(Q,P)=|Q|^2/(2M)+Q\cdot P/M$ and $J(P,Q)=M_{\rm in}^{\rm cl}(P+Q;Q)$,
--   $$
--   J(P,Q)=e^{-\beta E(Q,P)}J(P+Q,-Q),\qquad C\nu_{\rm EQ}(P)=0.
--   $$
--   The second identity holds wherever the gain and loss integrals are finite. It states stationarity of a momentum profile/formal multiplier, not a normalized trace-class infinite-volume Gibbs operator.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 16, §4.2.1: detailed balance and the stationary momentum profile, (4.7)–(4.13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF pp.15–16, (4.9)–(4.13): detailed balance and stationary momentum
profile. This is not an infinite-volume trace-class Gibbs state. -/
theorem maxwell_detailedBalance (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (hreciprocal : ∀ pf pi, crossSection d pf pi = crossSection d pi pf)
    (hplane : ∀ P Q, Integrable (rateIntegrand d F P Q)) :
    (∀ P Q, transferRate d F P Q = transferRate d F (P + Q) (-Q) *
      Real.exp (-beta * energyTransfer d.parameters Q P)) ∧
    (∀ P, Integrable (fun Q => transferRate d F (P - Q) Q *
        maxwell d.parameters.M beta (P - Q)) →
      Integrable (outgoingIntensity d F P) →
      classicalGenerator d F (maxwell d.parameters.M beta) P = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
