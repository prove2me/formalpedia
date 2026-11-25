-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_smul_measurePreserving
-- name    : ReciprocityTheory.AnForm.A.smul_measurePreserving
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:42.644413+00:00
-- url     : https://prove2.me/theorems/da3a983c-3b19-446c-acba-8e3e52ce993d
-- title:
--   A: smul measure Preserving
-- statement:
--   The A construction uses the smul measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L28-L37

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.smul_measurePreserving {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    MeasurePreserving (fun y : Fin D → ℂ => ζ • y) ∧
      MeasurableEmbedding (fun y : Fin D → ℂ => ζ • y) := by sorry
