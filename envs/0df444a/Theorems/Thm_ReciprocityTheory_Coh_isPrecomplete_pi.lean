-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_isPrecomplete_pi
-- name    : ReciprocityTheory.Coh.isPrecomplete_pi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:42.023719+00:00
-- url     : https://prove2.me/theorems/a369f2d7-ade1-4b06-887c-190349fd3db9
-- title:
--   Coh: is Precomplete pi
-- statement:
--   The Coh construction uses the is Precomplete pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L81-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L81-L99

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
variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

theorem ReciprocityTheory.Coh.isPrecomplete_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by sorry
