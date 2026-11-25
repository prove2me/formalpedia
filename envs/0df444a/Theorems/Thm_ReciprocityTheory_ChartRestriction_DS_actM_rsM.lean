-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_rsM
-- name    : ReciprocityTheory.ChartRestriction.DS.actM_rsM
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:52.050204+00:00
-- url     : https://prove2.me/theorems/e8b7d006-22e3-5585-b6c2-c73cb0454312
-- title:
--   DS: act M rs M
-- statement:
--   The DS construction uses the act M rs M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L97-L110

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

theorem ReciprocityTheory.ChartRestriction.DS.actM_rsM {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (fun a b => rsM (single a b (1 : ℂ))) X = rsM X := by sorry
