-- Prove2me | Theorems.Thm_TDLC_Refutation_path2_preserves
-- name    : TDLC.Refutation.path2_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:50.641807+00:00
-- url     : https://prove2.me/theorems/e5d1799c-dabf-569d-b8ba-a36cef431bcf
-- title:
--   Refutation: path2 preserves
-- statement:
--   The Refutation construction uses the path2 preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L135-L139
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L135-L139

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.path2_preserves {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by sorry
