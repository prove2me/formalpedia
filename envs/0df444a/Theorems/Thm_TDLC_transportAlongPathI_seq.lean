-- Prove2me | Theorems.Thm_TDLC_transportAlongPathI_seq
-- name    : TDLC.transportAlongPathI_seq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:14.15488+00:00
-- url     : https://prove2.me/theorems/54cf18fd-f7d6-5742-80e3-4fb97939458e
-- title:
--   TDLC: transport Along Path I seq
-- statement:
--   The TDLC construction uses the transport Along Path I seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L578-L582
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L578-L582

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.transportAlongPathI_seq {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.seq e hp) x y q =
      transportAlongPathI hp x y (transportAlongPresented e x y q) := by sorry
