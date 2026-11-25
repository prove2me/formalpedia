-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_sum_ins_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.sum_ins_succ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:05.007733+00:00
-- url     : https://prove2.me/theorems/321b8678-0289-4c99-983a-fba58ce27cfb
-- title:
--   OSAux: sum ins succ
-- statement:
--   The OSAux construction uses the sum ins succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L29-L39

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.sum_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) (g : ℂ → ℂ → ℂ) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((ins y z).2.1 j) ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((tailPt y).2.1 j) ((tailPt y).1 j) else 0 := by sorry
