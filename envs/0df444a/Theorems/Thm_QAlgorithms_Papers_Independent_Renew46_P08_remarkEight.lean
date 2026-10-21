-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkEight
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkEight
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:03:17.830467+00:00
-- url     : https://prove2.me/theorems/b08a3f41-dd0d-41cc-840d-1a60e4ea76b1
-- title:
--   Remark 8: uniform energy-bounded discrete continuity
-- statement:
--   Let $H\ge0$ satisfy the Gibbs condition, let $\widehat F$ be a regular sublinear entropy majorant, and fix $E>E_0$. The scalar limit $x\widehat F(E/x)\to0$ as $x\downarrow0$ implies that chi is finite and $D_*$-uniformly continuous on all countable ensembles with average energy at most $E$:
--
--   $$\forall\eta>0\ \exists\delta>0,\quad D_*(\mu,\nu)<\delta\Longrightarrow|\chi(\mu)-\chi(\nu)|<\eta.$$
--
--   The quantifiers range over the whole average-energy set, with no restriction on label count or on individual signal energies.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 28, Remark 8: uniform energy-bounded discrete continuity

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

/-- Remark 8, PDF p.28: Dstar-uniform continuity under AVERAGE energy only,
with no bound on label count or the coefficientEnergy of each individual signal. -/
theorem remarkEight {I : Type} [Countable I] [Nonempty I]
    (e : I → ℝ≥0) (he : SpectralGibbsCondition e) (F : ℝ → ℝ) (hF : EntropyMajorant e F)
    (E : ℝ) (hE : ground e < E) :
    Tendsto (fun x : ℝ => x * F (E/x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    UniformChiOn distanceStar {mu | coefficientEnergy e (countableAverage mu) ≤ ENNReal.ofReal E} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
