-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_compact_eq_d1a3cdb552e8
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_compact_eq_d1a3cdb552e8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:22.097962+00:00
-- url     : https://prove2.me/theorems/b10e1714-9201-43cc-8f69-e8c71fa815c6
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure compact eq d1a3cdb552e8: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure compact eq d1a3cdb5
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure compact eq d1a3cdb552e8 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure compact eq d1a3cdb552e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L168-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L168-L241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_compact_eq_d1a3cdb552e8 {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hne : Nonempty (ChartPartition A)) (hΦ : ∀ i, IsPotential A (Φ i))
    (hPsh : ∀ i, IsPsh A (Φ i)) {K : Set X} (hK : IsCompact K) :
    maMeasure A Φ K = ENNReal.ofReal (mInt A Φ (K.indicator 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«maMeasure_compact_eq» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_compact_eq_d1a3cdb552e8
