-- Prove2me | Theorems.Thm_TDLC_Refutation_badLeft_grade
-- name    : TDLC.Refutation.badLeft_grade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:54.872699+00:00
-- url     : https://prove2.me/theorems/27d702d1-a642-5383-b7cf-3dde5bb1b925
-- title:
--   Refutation: bad Left grade
-- statement:
--   The Refutation construction uses the bad Left grade property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L192-L198
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L192-L198

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.badLeft_grade : pathGrade dihedral diagonalMarker badLeft valuation = 1 := by sorry
