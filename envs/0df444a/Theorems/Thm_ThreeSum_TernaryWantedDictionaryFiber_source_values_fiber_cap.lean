-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_source_values_fiber_cap
-- name    : ThreeSum.TernaryWantedDictionaryFiber.source_values_fiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:39:01.142881+00:00
-- url     : https://prove2.me/theorems/75b56eaf-01c6-4e92-b474-9cb47e8abe4e
-- title:
--   Ternary Wanted Dictionary Fiber: source values fiber cap
-- statement:
--   The Ternary Wanted Dictionary Fiber construction uses the source values fiber cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L60-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedDictionaryFiber.lean#L60-L69

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers

theorem ThreeSum.TernaryWantedDictionaryFiber.source_values_fiber_cap {L p : ℕ} [Fact p.Prime]
    {α : TernaryJointType.DigitType} {I : Type*} [Fintype I] [DecidableEq I]
    (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2<p) (J : ℕ) (x : ℤ) :
    ((values (p : ℤ)
      ((TernaryCanonicalDictionaries.records (α := α) right maps B).map
        (TernaryCanonicalDictionaries.native right maps)) J).filter
      (fun z => (p : ℤ)^J ∣ x-z)).length ≤ (Fintype.card I*B)^J := by sorry
