-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
-- name    : ReciprocityTheory.Coh.admissibility_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:40.637317+00:00
-- url     : https://prove2.me/theorems/6a1262b9-31c4-4438-a0f2-fbbae83be4bc
-- title:
--   Coh: admissibility holds
-- statement:
--   The Coh construction uses the admissibility holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PairHomFCoeOfId.lean#L30-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PairHomFCoeOfId.lean#L30-L60

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal
universe u

theorem ReciprocityTheory.Coh.admissibility_holds : AdmStatement.{u} := by sorry
