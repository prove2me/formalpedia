-- Prove2me | Theorems.Thm_TDLC_Refutation_pathGrade_concat
-- name    : TDLC.Refutation.pathGrade_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:26.829367+00:00
-- url     : https://prove2.me/theorems/62b7bcca-71b2-422b-8f6c-8d86f8f733e9
-- title:
--   Refutation: path Grade concat
-- statement:
--   The Refutation construction uses the path Grade concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L74-L79
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L74-L79

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.pathGrade_concat {A : Type u} {x y z : A} (p : Path x y) (q : Path y z)
    (val : A → G) : pathGrade g mark (p ++ₚ q) val =
      g.mul (pathGrade g mark p val) (pathGrade g mark q val) := by sorry
