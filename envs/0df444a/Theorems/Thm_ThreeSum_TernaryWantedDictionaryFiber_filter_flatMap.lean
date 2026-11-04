-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_filter_flatMap
-- name    : ThreeSum.TernaryWantedDictionaryFiber.filter_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:37.739209+00:00
-- url     : https://prove2.me/theorems/187cca5e-071a-4493-bcad-3ac316174999
-- title:
--   Ternary Wanted Dictionary Fiber: filter flat Map
-- statement:
--   The Ternary Wanted Dictionary Fiber construction uses the filter flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L6-L10
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L6-L10

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers

theorem ThreeSum.TernaryWantedDictionaryFiber.filter_flatMap {A B : Type*} (xs : List A) (f : A → List B) (q : B → Bool) :
    (xs.flatMap f).filter q = xs.flatMap (fun x => (f x).filter q) := by sorry
