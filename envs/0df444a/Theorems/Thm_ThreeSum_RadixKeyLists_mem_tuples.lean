-- Prove2me | Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples
-- name    : ThreeSum.RadixKeyLists.mem_tuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:05.108115+00:00
-- url     : https://prove2.me/theorems/2765317b-bd26-4d5e-ba99-7d7fc31104ce
-- title:
--   Radix Key Lists: mem tuples
-- statement:
--   The Radix Key Lists construction uses the mem tuples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L62-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L62-L76

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}

theorem ThreeSum.RadixKeyLists.mem_tuples (base : List α) (j : ℕ) (xs : List α) :
    xs ∈ tuples base j ↔ xs.length=j ∧ ∀ a ∈ xs, a ∈ base := by sorry
