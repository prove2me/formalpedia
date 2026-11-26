-- Prove2me | Theorems.Thm_TDLC_Refutation_pathGrade_embed
-- name    : TDLC.Refutation.pathGrade_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:24.93928+00:00
-- url     : https://prove2.me/theorems/76ad931d-af25-4347-9e34-0f109c835a38
-- title:
--   Refutation: path Grade embed
-- statement:
--   The Refutation construction uses the path Grade embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L71-L72
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L71-L72

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.pathGrade_embed {A : Type u} {x y : A} (s : Step x y) (val : A → G) :
    pathGrade g mark (Path.lEmbed s) val = grade g mark s val := by sorry
