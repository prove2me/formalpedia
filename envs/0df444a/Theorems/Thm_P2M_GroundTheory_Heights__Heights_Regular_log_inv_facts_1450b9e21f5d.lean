-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:41.294951+00:00
-- url     : https://prove2.me/theorems/9fb61f12-c7d5-4725-8cb9-2490616d84ac
-- title:
--   P2 M Ground Theory Heights  Heights Regular log inv facts 1450b9e21f5d: P2 M Ground Theory Heights  Heights Regular log inv facts 1450b9e21f5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular log inv facts 1450b9e21f5d construction uses the P2 M Ground Theory Heights  Heights Regular log inv facts 1450b9e21f5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartComparison.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartComparison.lean#L16-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
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
open Metric
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' polyMax_mono')
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hta : t < Real.exp (-(Real.exp 1 + 2 * a))) :
    Real.exp 1 + 2 * a < Real.log t⁻¹ ∧ 1 < Real.log (Real.log t⁻¹) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«log_inv_facts» := P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d
