-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_hd_zero_fun
-- name    : ReciprocityTheory.Coh.hd_zero_fun
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:09.682397+00:00
-- url     : https://prove2.me/theorems/51bb1467-a039-4e45-8c02-86a6ad5a73a8
-- title:
--   Coh: hd zero fun
-- statement:
--   The Coh construction uses the hd zero fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L48-L49

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

theorem ReciprocityTheory.Coh.hd_zero_fun (n : ℕ) (x : Fin (n + 2) → X) : hd n (fun _ : Fin (n + 1) → X => (0 : V)) x = 0 := by sorry
