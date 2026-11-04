-- Prove2me | Theorems.Thm_ThreeSum_RadixKeyLists_values_eq_map
-- name    : ThreeSum.RadixKeyLists.values_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:03.270486+00:00
-- url     : https://prove2.me/theorems/653b94c9-5575-47b1-b575-af78b9bb64ea
-- title:
--   Radix Key Lists: values eq map
-- statement:
--   The Radix Key Lists construction uses the values eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L92-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L92-L100

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}

theorem ThreeSum.RadixKeyLists.values_eq_map (p : ℤ) (raw : α → ℤ) (base : List α) (j : ℕ) :
    values p (base.map raw) j = (tuples base j).map (Radix.positionalHash p raw) := by sorry
