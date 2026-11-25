-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_hd_one_eval
-- name    : ReciprocityTheory.Coh.hd_one_eval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:21.667508+00:00
-- url     : https://prove2.me/theorems/6851c53b-ac46-5734-86c8-1d242cc003d6
-- title:
--   Coh: hd one eval
-- statement:
--   The Coh construction uses the hd one eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L105-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L105-L115

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
variable {V X Y : Type u} [AddCommGroup V]

theorem ReciprocityTheory.Coh.hd_one_eval (F : (Fin 2 → X) → V) (z : Fin 3 → X) :
    hd 1 F z = F ![z 1, z 2] - F ![z 0, z 2] + F ![z 0, z 1] := by sorry
