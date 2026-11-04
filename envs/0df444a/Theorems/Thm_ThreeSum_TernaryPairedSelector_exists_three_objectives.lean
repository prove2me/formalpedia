-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSelector_exists_three_objectives
-- name    : ThreeSum.TernaryPairedSelector.exists_three_objectives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:34.3773+00:00
-- url     : https://prove2.me/theorems/3cfa19ee-7add-47d7-bd20-eec949a0420d
-- title:
--   Ternary Paired Selector: exists three objectives
-- statement:
--   The Ternary Paired Selector construction uses the exists three objectives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSelector.lean#L16-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSelector.lean#L16-L52

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedSelector
open Finset
open scoped BigOperators
variable {Ω : Type*} [DecidableEq Ω]

theorem ThreeSum.TernaryPairedSelector.exists_three_objectives (S : Finset Ω) (hS : S.Nonempty)
    (f : Fin 3 → Ω → ℚ) (normalizer : Fin 3 → ℚ)
    (hf : ∀ i seed, 0 ≤ f i seed) (hN : ∀ i, 0 ≤ normalizer i)
    (havg : ∀ i, (∑ seed ∈ S, f i seed) ≤ S.card*normalizer i) :
    ∃ seed ∈ S, ∀ i, f i seed ≤ 3*normalizer i := by sorry
