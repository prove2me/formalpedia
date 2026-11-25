-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_avg_re_affine
-- name    : ReciprocityTheory.AnForm.A.PshInh.avg_re_affine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:36.77707+00:00
-- url     : https://prove2.me/theorems/1e3df8a0-577b-4175-8866-d4f0e0dc6b6e
-- title:
--   Psh Inh: avg re affine
-- statement:
--   The Psh Inh construction uses the avg re affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshBasic.lean#L139-L147

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

theorem ReciprocityTheory.AnForm.A.PshInh.avg_re_affine (a b c : ℂ) :
    Real.circleAverage (fun ζ : ℂ => (c * (a + ζ * b)).re) 0 1 = (c * a).re := by sorry
