-- Prove2me | Theorems.Thm_TDLC_Refutation_notStepNat
-- name    : TDLC.Refutation.notStepNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:27.745548+00:00
-- url     : https://prove2.me/theorems/5f600b5c-2b9f-57d9-8846-44a48982d007
-- title:
--   Refutation: not Step Nat
-- statement:
--   The Refutation construction uses the not Step Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L225-L227
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L225-L227

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.notStepNat : ¬ Nonempty StepNat := by sorry
