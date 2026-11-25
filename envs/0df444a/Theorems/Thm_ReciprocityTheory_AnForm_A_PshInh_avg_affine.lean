-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_avg_affine
-- name    : ReciprocityTheory.AnForm.A.PshInh.avg_affine
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:05.342615+00:00
-- url     : https://prove2.me/theorems/9c6a4279-1e46-4c2f-85da-f4f53141c6c2
-- title:
--   Psh Inh: avg affine
-- statement:
--   The Psh Inh construction uses the avg affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L134-L137

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
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshInh
open MeasureTheory Metric Set Filter Topology Real
noncomputable section

theorem ReciprocityTheory.AnForm.A.PshInh.avg_affine (a b : ℂ) : Real.circleAverage (fun ζ : ℂ => a + ζ * b) 0 1 = a := by sorry
