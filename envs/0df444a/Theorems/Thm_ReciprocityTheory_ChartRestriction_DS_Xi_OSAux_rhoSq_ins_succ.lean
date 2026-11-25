-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_rhoSq_ins_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ins_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:59.070158+00:00
-- url     : https://prove2.me/theorems/b629da16-cff7-5cb6-a8dc-0e7eb16fa2d3
-- title:
--   OSAux: rho Sq ins succ
-- statement:
--   The OSAux construction uses the rho Sq ins succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L52-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    rhoSq (ins y z) i.succ = rhoSq (tailPt y) i.succ := by sorry
