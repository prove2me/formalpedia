-- Prove2me | Theorems.Thm_TDLC_evalHomotopyStepI_lamCong
-- name    : TDLC.evalHomotopyStepI_lamCong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:10.906616+00:00
-- url     : https://prove2.me/theorems/ace4373b-5f53-4253-ab7b-6be3bc95c8e5
-- title:
--   TDLC: eval Homotopy Step I lam Cong
-- statement:
--   The TDLC construction uses the eval Homotopy Step I lam Cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L413-L417
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L413-L417

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.evalHomotopyStepI_lamCong {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.lamCong e)).family x =
      Step.apCong (fun k : A → B => k x)
        (Step.lamCong (evalHomotopyStepI e).family) := by sorry
