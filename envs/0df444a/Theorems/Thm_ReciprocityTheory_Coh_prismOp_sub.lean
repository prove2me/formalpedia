-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_prismOp_sub
-- name    : ReciprocityTheory.Coh.prismOp_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:54.646728+00:00
-- url     : https://prove2.me/theorems/4cbf22db-aff9-4075-8b3a-e33f688eddb6
-- title:
--   Coh: prism Op sub
-- statement:
--   The Coh construction uses the prism Op sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L66-L73

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

theorem ReciprocityTheory.Coh.prismOp_sub (a b : X → Y) (n : ℕ) : ∀ (F G : (Fin (n + 2) → Y) → V) (x : Fin (n + 1) → X),
    prismOp a b n (fun y => F y - G y) x = prismOp a b n F x - prismOp a b n G x := by sorry
