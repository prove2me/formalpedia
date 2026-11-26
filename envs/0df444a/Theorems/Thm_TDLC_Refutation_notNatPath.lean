-- Prove2me | Theorems.Thm_TDLC_Refutation_notNatPath
-- name    : TDLC.Refutation.notNatPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:29.165878+00:00
-- url     : https://prove2.me/theorems/bb4c9c04-34e7-57ec-97f8-443d699fdc76
-- title:
--   Refutation: not Nat Path
-- statement:
--   The Refutation construction uses the not Nat Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L235-L238
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L235-L238

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.notNatPath : ¬ Nonempty NatPath := by sorry
