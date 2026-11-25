-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero_fun
-- name    : ReciprocityTheory.Coh.prismOp_zero_fun
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:05.01114+00:00
-- url     : https://prove2.me/theorems/ea4485a6-c679-5e0b-a18b-22b20858e99d
-- title:
--   Coh: prism Op zero fun
-- statement:
--   The Coh construction uses the prism Op zero fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L75-L79

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

theorem ReciprocityTheory.Coh.prismOp_zero_fun (a b : X → Y) (n : ℕ) : ∀ (x : Fin (n + 1) → X),
    prismOp a b n (fun _ => (0 : V)) x = 0 := by sorry
