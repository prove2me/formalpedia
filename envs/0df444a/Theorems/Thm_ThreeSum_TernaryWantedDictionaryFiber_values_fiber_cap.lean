-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_values_fiber_cap
-- name    : ThreeSum.TernaryWantedDictionaryFiber.values_fiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:42.53708+00:00
-- url     : https://prove2.me/theorems/161c8536-ba93-4796-979c-5cf2d30d0a87
-- title:
--   Ternary Wanted Dictionary Fiber: values fiber cap
-- statement:
--   The Ternary Wanted Dictionary Fiber construction uses the values fiber cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L55-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L55-L59

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers

theorem ThreeSum.TernaryWantedDictionaryFiber.values_fiber_cap (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) (C : ℕ)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) (J : ℕ) (x : ℤ) :
    ((values p raws J).filter (fun z => p^J ∣ x-z)).length ≤ C^J := by sorry
