-- Prove2me | Theorems.Thm_TDLC_evalHomotopyPathI_seq
-- name    : TDLC.evalHomotopyPathI_seq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:14.706883+00:00
-- url     : https://prove2.me/theorems/8affc33b-9e1b-4ae5-a572-28f8946f563c
-- title:
--   TDLC: eval Homotopy Path I seq
-- statement:
--   The TDLC construction uses the eval Homotopy Path I seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L443-L446
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L443-L446

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.evalHomotopyPathI_seq {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k) (x : A) :
    evalHomotopyPathI (.seq e hp) x =
      Path.seq ((evalHomotopyStepI e).family x) (evalHomotopyPathI hp x) := by sorry
