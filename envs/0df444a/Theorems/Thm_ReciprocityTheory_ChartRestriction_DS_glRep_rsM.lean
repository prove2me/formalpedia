-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_glRep_rsM
-- name    : ReciprocityTheory.ChartRestriction.DS.glRep_rsM
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:03.592729+00:00
-- url     : https://prove2.me/theorems/a3871fd3-e84b-4fe2-be15-4db117e34cce
-- title:
--   DS: gl Rep rs M
-- statement:
--   The DS construction uses the gl Rep rs M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L122-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.glRep_rsM (n : ℕ) : IsGlRep (fun a b : Fin n => rsM (single a b (1 : ℂ))) := by sorry
