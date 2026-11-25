-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_proof_3bd5ae614b76
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_proof_3bd5ae614b76
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:55.798265+00:00
-- url     : https://prove2.me/theorems/e798b056-77a4-48d8-8022-59e0315b454e
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Log Regularisation proof 3bd5ae614b76: P2 M Ground Theory Heights  Heights Regular Log Log Regularisation proof 3bd5ae614b76
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Log Regularisation proof 3bd5ae614b76 construction uses the P2 M Ground Theory Heights  Heights Regular Log Log Regularisation proof 3bd5ae614b76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ChartFun.lean#L35-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ChartFun.lean#L35-L248

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartFun
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

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
open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}

theorem P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_proof_3bd5ae614b76 (h0 : GlueRegularised.Statement) (h1 : ChartComparison.Statement)
    (h2 : MollifiedNearSmooth.Statement) (h3 : CutoffsExist.Statement)
    (h4 : ChartMollifiedBounds.Statement) : LogLogRegularisation.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogLogRegularisation».«proof» := P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_proof_3bd5ae614b76
