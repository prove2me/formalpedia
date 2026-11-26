-- Prove2me | Theorems.Thm_TDLC_evalHomotopyStepI_trans
-- name    : TDLC.evalHomotopyStepI_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:08.038043+00:00
-- url     : https://prove2.me/theorems/c8a067c7-90be-50b1-9b22-350a649a5a8c
-- title:
--   TDLC: eval Homotopy Step I trans
-- statement:
--   The TDLC construction uses the eval Homotopy Step I trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L407-L411
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L407-L411

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.evalHomotopyStepI_trans {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (d : HomotopyStepI g k) (x : A) :
    (evalHomotopyStepI (.trans e d)).family x =
      Step.trans ((evalHomotopyStepI e).family x)
        ((evalHomotopyStepI d).family x) := by sorry
