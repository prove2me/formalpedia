-- Prove2me | Theorems.Thm_TDLC_Refutation_grade_constantBeta
-- name    : TDLC.Refutation.grade_constantBeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:32.977876+00:00
-- url     : https://prove2.me/theorems/46f6162a-760d-4c7e-adae-265f47391d6d
-- title:
--   Refutation: grade constant Beta
-- statement:
--   The Refutation construction uses the grade constant Beta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L184-L190
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean#L184-L190

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

theorem TDLC.Refutation.grade_constantBeta (x a : Fin 3) :
    grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => x) a) valuation =
      dMul (dInv (valuation x)) (valuation a) := by sorry
