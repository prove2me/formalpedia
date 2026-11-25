-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_sumR_ins_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.sumR_ins_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:02.419455+00:00
-- url     : https://prove2.me/theorems/8a460983-a3ac-5df4-996c-11b69931633f
-- title:
--   OSAux: sum R ins succ
-- statement:
--   The OSAux construction uses the sum R ins succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L41-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.sumR_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(ins y z).2.1 j‖ ^ 2 else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(tailPt y).2.1 j‖ ^ 2 else 0 := by sorry
