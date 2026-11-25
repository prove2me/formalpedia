-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_hd_zero_eval
-- name    : ReciprocityTheory.Coh.hd_zero_eval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:14.541068+00:00
-- url     : https://prove2.me/theorems/6db9c4ed-e638-4eef-b386-201814362d51
-- title:
--   Coh: hd zero eval
-- statement:
--   The Coh construction uses the hd zero eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L101-L103

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

theorem ReciprocityTheory.Coh.hd_zero_eval (G : (Fin 1 → X) → V) (x : Fin 2 → X) : hd 0 G x = G ![x 1] - G ![x 0] := by sorry
