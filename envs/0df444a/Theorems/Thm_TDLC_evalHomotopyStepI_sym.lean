-- Prove2me | Theorems.Thm_TDLC_evalHomotopyStepI_sym
-- name    : TDLC.evalHomotopyStepI_sym
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:05.581208+00:00
-- url     : https://prove2.me/theorems/1ba1a0c9-ef43-4d44-9300-8fa297f3a9d2
-- title:
--   TDLC: eval Homotopy Step I sym
-- statement:
--   The TDLC construction uses the eval Homotopy Step I sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L402-L405
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L402-L405

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.evalHomotopyStepI_sym {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.sym e)).family x =
      Step.sym ((evalHomotopyStepI e).family x) := by sorry
