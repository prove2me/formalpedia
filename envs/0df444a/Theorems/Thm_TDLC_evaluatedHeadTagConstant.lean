-- Prove2me | Theorems.Thm_TDLC_evaluatedHeadTagConstant
-- name    : TDLC.evaluatedHeadTagConstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:42.206883+00:00
-- url     : https://prove2.me/theorems/38f1b285-a6bc-4d7d-83e9-327a46adfcc2
-- title:
--   TDLC: evaluated Head Tag Constant
-- statement:
--   A global presentation evaluates to the same outer step form at every point.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L646-L650
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L646-L650

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.evaluatedHeadTagConstant {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) :
    Step.headTag ((evalHomotopyStepI e).family x) =
      Step.headTag ((evalHomotopyStepI e).family y) := by sorry
