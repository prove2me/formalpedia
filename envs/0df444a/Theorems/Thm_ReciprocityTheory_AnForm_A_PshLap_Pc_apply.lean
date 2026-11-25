-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_Pc_apply
-- name    : ReciprocityTheory.AnForm.A.PshLap.Pc_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:14.345162+00:00
-- url     : https://prove2.me/theorems/318bc276-bcf1-5651-a410-95512248275c
-- title:
--   Psh Lap: Pc apply
-- statement:
--   The Psh Lap construction uses the Pc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L26-L27

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.PshLap.Pc_apply (w : Fin D → ℂ) (T : (Fin D → ℂ) →L[ℝ] ℝ) (a : ℂ) : Pc w T a = T (a • w) := by sorry
