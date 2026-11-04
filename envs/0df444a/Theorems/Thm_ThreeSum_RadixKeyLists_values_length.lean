-- Prove2me | Theorems.Thm_ThreeSum_RadixKeyLists_values_length
-- name    : ThreeSum.RadixKeyLists.values_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:15:56.755561+00:00
-- url     : https://prove2.me/theorems/458a0292-27a5-49fc-9c21-12ae55b05cca
-- title:
--   Radix Key Lists: values length
-- statement:
--   The Radix Key Lists construction uses the values length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L43-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L43-L47

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}

theorem ThreeSum.RadixKeyLists.values_length (p : ℤ) (base : List ℤ) (j : ℕ) :
    (values p base j).length=base.length^j := by sorry
