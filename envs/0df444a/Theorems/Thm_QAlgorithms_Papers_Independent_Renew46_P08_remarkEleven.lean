-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkEleven
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkEleven
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:08:00.032645+00:00
-- url     : https://prove2.me/theorems/81e845ee-21da-4414-ba35-2bd004afd383
-- title:
--   Remark 11: generalized energy-bounded uniform continuity
-- statement:
--   For a nonnegative Gibbs Hamiltonian, a regular sublinear entropy majorant $\widehat F$, and $E>E_0$, chi is finite and uniformly continuous in generalized Kantorovich distance on the entire set of generalized ensembles of average energy at most $E$. In particular,
--
--   $$\forall\eta>0\ \exists\delta>0\ \forall\mu,\nu,\quad E(\mu),E(\nu)\le E,\ D_K(\mu,\nu)<\delta\Longrightarrow|\chi(\mu)-\chi(\nu)|<\eta.$$
--
--   The scalar limit $x\widehat F(E/x)\to0$ is included. This is a uniform quantitative conclusion, stronger than merely saying that chi is continuous in a weak topology.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 32, Remark 11: generalized energy-bounded uniform continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Remark 11, PDF p.32: quantitative uniform continuity in the generalized
Kantorovich distance under a bound on the actual barycenter coefficientEnergy. -/
theorem remarkEleven {I : Type} [Countable I] [Nonempty I]
    (e : I → ℝ≥0) (he : SpectralGibbsCondition e) (F : ℝ → ℝ) (hF : EntropyMajorant e F)
    (E : ℝ) (hE : ground e < E) :
    Tendsto (fun x : ℝ => x * F (E/x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ mu : GeneralizedEnsemble I,
      coefficientEnergy e (averageCoefficients mu) ≤ ENNReal.ofReal E → ensembleHolevo id mu < ⊤) ∧
    (∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ mu nu : GeneralizedEnsemble I,
        coefficientEnergy e (averageCoefficients mu) ≤ ENNReal.ofReal E →
        coefficientEnergy e (averageCoefficients nu) ≤ ENNReal.ofReal E →
        generalizedK mu nu < ENNReal.ofReal delta →
        |(ensembleHolevo id mu).toReal - (ensembleHolevo id nu).toReal| < eta) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
