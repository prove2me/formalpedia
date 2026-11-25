-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_BoundedChartComparison_proof_38c3cfbe5458
-- name    : P2M_GroundTheory_Heights__Heights_Regular_BoundedChartComparison_proof_38c3cfbe5458
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:12.449077+00:00
-- url     : https://prove2.me/theorems/8999b14a-fc5e-44b1-9341-3ff4e5ea4766
-- title:
--   P2 M Ground Theory Heights  Heights Regular Bounded Chart Comparison proof 38c3cfbe5458: P2 M Ground Theory Heights  Heights Regular Bounded Chart Comparison proof 38c3cfbe5458
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Bounded Chart Comparison proof 38c3cfbe5458 construction uses the P2 M Ground Theory Heights  Heights Regular Bounded Chart Comparison proof 38c3cfbe5458 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartComparison.lean#L101-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartComparison.lean#L101-L238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_BoundedRegularisation_proof_73a4e2c90db9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969
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

theorem P2M_GroundTheory_Heights__Heights_Regular_BoundedChartComparison_proof_38c3cfbe5458 (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) : BoundedChartComparison.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«BoundedChartComparison».«proof» := P2M_GroundTheory_Heights__Heights_Regular_BoundedChartComparison_proof_38c3cfbe5458
