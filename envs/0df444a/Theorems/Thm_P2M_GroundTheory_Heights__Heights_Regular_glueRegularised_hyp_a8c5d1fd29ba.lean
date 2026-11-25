-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_glueRegularised_hyp_a8c5d1fd29ba
-- name    : P2M_GroundTheory_Heights__Heights_Regular_glueRegularised_hyp_a8c5d1fd29ba
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:35.936447+00:00
-- url     : https://prove2.me/theorems/b669c35e-631b-4f36-8246-bc6699645729
-- title:
--   P2 M Ground Theory Heights  Heights Regular glue Regularised hyp a8c5d1fd29ba: P2 M Ground Theory Heights  Heights Regular glue Regularised hyp a8c5d1fd29ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular glue Regularised hyp a8c5d1fd29ba construction uses the P2 M Ground Theory Heights  Heights Regular glue Regularised hyp a8c5d1fd29ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L414-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L414-L423

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
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
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_glueRegularised_hyp_a8c5d1fd29ba : ∃ ρ : Mollifier 0,
    pointReg.IsCutoffFamily (fun _ _ => 0) 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧
    (∀ j, ∀ x ∈ closure (pointReg.mid j), closedBall (pointReg.chart j x) 1 ⊆ (pointReg.chart j).target) ∧
    (∀ j k, ∀ x ∈ pointReg.mid j ∩ pointReg.mid k,
      |pointReg.phReg ρ 0 1 j x - pointReg.phReg ρ 0 1 k x| ≤ 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«glueRegularised_hyp» := P2M_GroundTheory_Heights__Heights_Regular_glueRegularised_hyp_a8c5d1fd29ba
