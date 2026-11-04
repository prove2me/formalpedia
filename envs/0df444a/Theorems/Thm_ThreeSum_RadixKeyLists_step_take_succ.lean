-- Prove2me | Theorems.Thm_ThreeSum_RadixKeyLists_step_take_succ
-- name    : ThreeSum.RadixKeyLists.step_take_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:50.002043+00:00
-- url     : https://prove2.me/theorems/12350168-f007-4132-9fed-6ce4314fb166
-- title:
--   Radix Key Lists: step take succ
-- statement:
--   The Radix Key Lists construction uses the step take succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L33-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L33-L37

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}

theorem ThreeSum.RadixKeyLists.step_take_succ (p : ℤ) (base prev : List ℤ) {i : ℕ} (hi : i < base.length) :
    step p (base.take (i+1)) prev = step p (base.take i) prev ++
      prev.map (fun y => base[i]+p*y) := by sorry
