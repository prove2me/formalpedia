-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMaxPsh_thm
-- name    : ReciprocityTheory.AnForm.A.regMaxPsh_thm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:04.53387+00:00
-- url     : https://prove2.me/theorems/e234e939-62cb-5d0c-ba65-d4028a310dc6
-- title:
--   A: reg Max Psh thm
-- statement:
--   The A construction uses the reg Max Psh thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L331-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L331-L336

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section

theorem ReciprocityTheory.AnForm.A.regMaxPsh_thm : RegMaxPshStatement := by sorry
