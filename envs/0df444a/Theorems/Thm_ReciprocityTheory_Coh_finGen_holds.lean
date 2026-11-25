-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_finGen_holds
-- name    : ReciprocityTheory.Coh.finGen_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:42.964738+00:00
-- url     : https://prove2.me/theorems/f59f56f9-03da-4e29-870a-36c13fc53546
-- title:
--   Coh: fin Gen holds
-- statement:
--   The Coh construction uses the fin Gen holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L206-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L206-L273

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u

theorem ReciprocityTheory.Coh.finGen_holds : FinGenStatement.{u} := by sorry
