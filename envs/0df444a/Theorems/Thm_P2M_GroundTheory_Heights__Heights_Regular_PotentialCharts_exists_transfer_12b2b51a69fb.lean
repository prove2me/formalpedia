-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_12b2b51a69fb
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_12b2b51a69fb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:46.073343+00:00
-- url     : https://prove2.me/theorems/0e4a9079-6768-4ebd-b908-0d686cd7996b
-- title:
--   P2 M Ground Theory Heights  Heights Regular Potential Charts exists transfer 12b2b51a69fb: P2 M Ground Theory Heights  Heights Regular Potential Charts exists transfer 12b2b51a69fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Potential Charts exists transfer 12b2b51a69fb construction uses the P2 M Ground Theory Heights  Heights Regular Potential Charts exists transfer 12b2b51a69fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartComparison.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartComparison.lean#L78-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

theorem P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_12b2b51a69fb [CompactSpace X] :
    ∃ δ > 0, ∃ L : ℝ, 1 ≤ L ∧ ∀ j k : Fin P.N, ∀ x ∈ P.mid j ∩ P.mid k,
      ∀ y ∈ closedBall (P.chart j x) δ,
      y ∈ (P.chart j).target ∧ (P.chart j).symm y ∈ (P.chart k).source ∧
      ‖P.chart k ((P.chart j).symm y) - P.chart k x‖ ≤ L * ‖y - P.chart j x‖ ∧
      P.q j y - P.q k (P.chart k ((P.chart j).symm y)) - (P.q j (P.chart j x) - P.q k (P.chart k x)) ≤
        L * ‖y - P.chart j x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PotentialCharts».«exists_transfer» := P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_transfer_12b2b51a69fb
