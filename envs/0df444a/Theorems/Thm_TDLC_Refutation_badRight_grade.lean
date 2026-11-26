-- Prove2me | Theorems.Thm_TDLC_Refutation_badRight_grade
-- name    : TDLC.Refutation.badRight_grade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:56.287725+00:00
-- url     : https://prove2.me/theorems/494d3446-a435-5220-8af3-a84bea777ccf
-- title:
--   Refutation: bad Right grade
-- statement:
--   The Refutation construction uses the bad Right grade property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L200-L206
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L200-L206

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.badRight_grade : pathGrade dihedral diagonalMarker badRight valuation = 2 := by sorry
