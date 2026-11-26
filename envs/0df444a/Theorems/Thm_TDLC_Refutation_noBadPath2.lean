-- Prove2me | Theorems.Thm_TDLC_Refutation_noBadPath2
-- name    : TDLC.Refutation.noBadPath2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:26.900185+00:00
-- url     : https://prove2.me/theorems/9c3c2f2d-3844-539e-8c05-6ddcdb9ae748
-- title:
--   Refutation: no Bad Path2
-- statement:
--   The Refutation construction uses the no Bad Path2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L208-L212
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L208-L212

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.noBadPath2 : ¬ Nonempty (Path2 badLeft badRight) := by sorry
