-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_flatMap_range_getD
-- name    : ThreeSum.TernaryWantedDictionaryFiber.flatMap_range_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:26.639209+00:00
-- url     : https://prove2.me/theorems/f3d6b4ae-2b0d-4a77-b24a-5caf82aecec5
-- title:
--   Ternary Wanted Dictionary Fiber: flat Map range get D
-- statement:
--   The Ternary Wanted Dictionary Fiber construction uses the flat Map range get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L18-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L18-L20

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers

theorem ThreeSum.TernaryWantedDictionaryFiber.flatMap_range_getD (xs : List ℤ) {A : Type*} (f : ℤ → List A) :
    xs.flatMap f=(List.range xs.length).flatMap (fun i => f (xs.getD i 0)) := by sorry
