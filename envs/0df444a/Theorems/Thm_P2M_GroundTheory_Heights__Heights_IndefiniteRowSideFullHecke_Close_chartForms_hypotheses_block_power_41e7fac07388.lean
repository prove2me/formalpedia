-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForms_hypotheses_block_power_41e7fac07388
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForms_hypotheses_block_power_41e7fac07388
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:01.237743+00:00
-- url     : https://prove2.me/theorems/a7615503-bf69-436d-8cf6-1ce7f6820736
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Forms hypotheses block power 41e7fac07388: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Forms hypotheses block power 41e7fac07388 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Forms hypotheses block power 41e7fac07388 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L367-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L367-L370

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData
variable (n)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForms_hypotheses_block_power_41e7fac07388 (k₀ : ι) :
    (blockPowLine n k₀ 1).deg = (powBlock n k₀ 1).deg ∧
      ∀ c j, (powBlock n k₀ 1).lift ((powChartForms n k₀ 1).g c j) ∉ (powBlock n k₀ 1).ext := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«chartForms_hypotheses_block_power» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForms_hypotheses_block_power_41e7fac07388
