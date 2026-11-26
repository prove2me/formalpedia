-- Prove2me | Theorems.Thm_TDLC_Refutation_pathGrade_ap
-- name    : TDLC.Refutation.pathGrade_ap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:28.216798+00:00
-- url     : https://prove2.me/theorems/915469d8-dc8e-400d-a24d-57aa26b2f4bb
-- title:
--   Refutation: path Grade ap
-- statement:
--   The Refutation construction uses the path Grade ap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L81-L86
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L81-L86

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.pathGrade_ap {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) (val : B → G) :
    pathGrade g mark (Path.ap f p) val = pathGrade g mark p (fun x => val (f x)) := by sorry
