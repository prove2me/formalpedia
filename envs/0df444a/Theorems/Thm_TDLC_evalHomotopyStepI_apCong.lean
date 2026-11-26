-- Prove2me | Theorems.Thm_TDLC_evalHomotopyStepI_apCong
-- name    : TDLC.evalHomotopyStepI_apCong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:04.892877+00:00
-- url     : https://prove2.me/theorems/93a38210-9d90-59a1-bbac-097b6513efd8
-- title:
--   TDLC: eval Homotopy Step I ap Cong
-- statement:
--   The TDLC construction uses the eval Homotopy Step I ap Cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L397-L400
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L397-L400

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.evalHomotopyStepI_apCong {A B C : Type u} (v : B → C)
    {f g : A → B} (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.apCong v e)).family x =
      Step.apCong v ((evalHomotopyStepI e).family x) := by sorry
