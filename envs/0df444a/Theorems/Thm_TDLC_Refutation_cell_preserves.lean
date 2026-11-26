-- Prove2me | Theorems.Thm_TDLC_Refutation_cell_preserves
-- name    : TDLC.Refutation.cell_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:48.900866+00:00
-- url     : https://prove2.me/theorems/7079c949-b872-563e-b09e-feb99eb0c8cd
-- title:
--   Refutation: cell preserves
-- statement:
--   The Refutation construction uses the cell preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L88-L133
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L88-L133

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.cell_preserves {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by sorry
