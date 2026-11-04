-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_filtered_values
-- name    : ThreeSum.TernaryWantedDictionaryFiber.filtered_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:18.521275+00:00
-- url     : https://prove2.me/theorems/786f39a9-7f3c-4a2b-9b53-b00709e73d8c
-- title:
--   Ternary Wanted Dictionary Fiber: filtered values
-- statement:
--   Exact list equality, rather than just existence: every repeated dictionary
--   key corresponds to its own carry-compatible tuple occurrence.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L24-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L24-L53

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers

theorem ThreeSum.TernaryWantedDictionaryFiber.filtered_values (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) :
    ∀ j x, (values p raws j).filter (fun z => p^j ∣ x-z)=
      (wantedOutputs p raws j x).map (Radix.positionalHash p (fun i => raws.getD i 0)) := by sorry
