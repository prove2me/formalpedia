-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_rhoSq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_rhoSq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:45.246095+00:00
-- url     : https://prove2.me/theorems/d2204a7d-07a6-4d78-97b4-a143e8fbbe9d
-- title:
--   OSAux: cont rho Sq
-- statement:
--   The OSAux construction uses the cont rho Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L204-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean#L204-L212

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by sorry
