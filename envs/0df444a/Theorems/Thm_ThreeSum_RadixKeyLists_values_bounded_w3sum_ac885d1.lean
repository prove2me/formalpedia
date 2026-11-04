-- Prove2me | Theorems.Thm_ThreeSum_RadixKeyLists_values_bounded_w3sum_ac885d1
-- name    : ThreeSum.RadixKeyLists.values_bounded_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:51.1273+00:00
-- url     : https://prove2.me/theorems/725ba976-ae52-4499-95bf-fcba5c99ce08
-- title:
--   Radix Key Lists: values bounded
-- statement:
--   The Radix Key Lists construction uses the values bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L102-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RadixKeyLists.lean#L102-L127

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
set_option autoImplicit false
open ThreeSum ThreeSum.RadixKeyLists
variable {α β : Type*}

theorem ThreeSum.RadixKeyLists.values_bounded_w3sum_ac885d1 (p U : ℕ) (base : List ℤ)
    (hbase : ∀ x ∈ base, |x| ≤ (U : ℤ)) (j : ℕ) :
    ∀ z ∈ values (p : ℤ) base j, |z| ≤ ((U*(p+1)^j : ℕ) : ℤ) := by sorry
