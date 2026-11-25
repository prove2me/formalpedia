-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero_eval
-- name    : ReciprocityTheory.Coh.prismOp_zero_eval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:58:07.255886+00:00
-- url     : https://prove2.me/theorems/60ade3a7-1445-4a57-80e5-7c4f975a1fee
-- title:
--   Coh: prism Op zero eval
-- statement:
--   The Coh construction uses the prism Op zero eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L117-L119

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

theorem ReciprocityTheory.Coh.prismOp_zero_eval (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F ![a (x 0), b (x 0)] := by sorry
