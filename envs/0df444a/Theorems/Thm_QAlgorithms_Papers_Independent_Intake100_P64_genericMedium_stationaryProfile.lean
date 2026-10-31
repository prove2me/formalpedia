-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_genericMedium_stationaryProfile
-- name    : QAlgorithms.Papers.Independent.Intake100.P64.genericMedium_stationaryProfile
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:33:06.86735+00:00
-- url     : https://prove2.me/theorems/c3a3de55-a376-4820-8496-8683afdec766
-- title:
--   §8.2.3: detailed balance implies stationary momentum profile, (8.22)–(8.23)
-- statement:
--   Let $m,M,\hbar,n_{\rm gas}>0$ denote the gas mass, tracer mass, Planck constant, and gas number density, and put $m_*=mM/(m+M)$. Momenta lie in $\mathbb R^3$. The gas law $\mu$ is a nonnegative measurable Lebesgue probability density, $f(p_f,p_i)$ is the elastic scattering amplitude entering the collision model, and $\sigma=|f|^2$. This is the ideal homogeneous stationary dilute-gas model with elastic two-body scattering and negligible gas degeneracy. Plane integrals use Euclidean area on $Q^\perp$. Each displayed finite scalar integral is understood on its measurable, absolutely integrable domain. Kernel identities use specified representatives, not point evaluation of an arbitrary $L^2$ class.
--
--   For a thermal gas, $\beta>0$, $\mu_\beta(p)=(\beta/(2\pi m))^{3/2}e^{-\beta|p|^2/(2m)}$, $\nu_{\rm EQ}(P)=(\beta/(2\pi M))^{3/2}e^{-\beta|P|^2/(2M)}$, and $v_\beta=\sqrt{2/(\beta m)}$.
--
--   Let $S(Q,P)\ge0$ describe a medium and obey $S(Q,P)=e^{-\beta E(Q,P)}S(-Q,P+Q)$. Assume reciprocal scattering and finite transverse scattering averages and total collision integrals. With $\sigma_{\rm av}$ as in (8.6),
--   $$
--   \frac{n_{\rm gas}}{m_*^2}\int dQ\,\sigma_{\rm av}(P,Q)\big[S(Q,P-Q)\nu_{\rm EQ}(P-Q)-S(Q,P)\nu_{\rm EQ}(P)\big]=0.
--   $$
--   Thus the classical collision expression and the corresponding formal quantum momentum multiplier annihilate the canonical profile. Only detailed balance and reversal symmetry are used; no Maxwell functional form is assumed for $S$, and no infinite-volume trace-class state is inferred.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, PDF p. 48, §8.2.3: detailed balance implies stationary momentum profile, (8.22)–(8.23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.48, (8.22)–(8.23): detailed balance, without the Maxwell shape
of S, annihilates the canonical momentum profile. Reciprocity of scattering
is retained, and this is not a trace-class Gibbs-state assertion. -/
theorem genericMedium_stationaryProfile (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta) (S : Momentum → Momentum → ℝ)
    (hS : ∀ Q P, 0 ≤ S Q P)
    (hbalance : ∀ Q P, S Q P = Real.exp (-beta * energyTransfer d.parameters Q P) * S (-Q) (P + Q))
    (hreciprocal : ∀ pf pi, crossSection d pf pi = crossSection d pi pf)
    (hplane : ∀ P Q, Integrable (fun k : TransversePlane =>
      maxwellPlane d.parameters.m beta (F.map Q k) * crossSection d
        (transverseRelative d.parameters (F.map Q k) P Q - (1 / 2 : ℝ) • Q)
        (transverseRelative d.parameters (F.map Q k) P Q + (1 / 2 : ℝ) • Q)))
    (P : Momentum)
    (hintegrable : Integrable (fun Q => averagedCrossSection d F beta P Q *
      (S Q (P - Q) * maxwell d.parameters.M beta (P - Q) -
        S Q P * maxwell d.parameters.M beta P))) :
    structureGenerator d F beta S (maxwell d.parameters.M beta) P = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P64

end
