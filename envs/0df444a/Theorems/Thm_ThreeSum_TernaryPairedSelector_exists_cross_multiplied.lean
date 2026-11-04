-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSelector_exists_cross_multiplied
-- name    : ThreeSum.TernaryPairedSelector.exists_cross_multiplied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:42.527165+00:00
-- url     : https://prove2.me/theorems/ab9a62ad-29d0-49b5-a69e-6d6aeb471844
-- title:
--   Ternary Paired Selector: exists cross multiplied
-- statement:
--   The exact integer test used by the actual selector. Its three expected
--   contractions each carry the factor three from conditioning on admissibility;
--   simultaneous selection therefore gives the paid factor nine.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSelector.lean#L57-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSelector.lean#L57-L82

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedSelector
open Finset
open scoped BigOperators
variable {Ω : Type*} [DecidableEq Ω]

theorem ThreeSum.TernaryPairedSelector.exists_cross_multiplied (S : Finset Ω) (hS : S.Nonempty)
    (f : Fin 3 → Ω → ℕ) (numerator denominator : Fin 3 → ℕ)
    (hd : ∀ i, 0 < denominator i)
    (havg : ∀ i, denominator i*(∑ seed ∈ S, f i seed) ≤ 3*S.card*numerator i) :
    ∃ seed ∈ S, ∀ i, denominator i*f i seed ≤ 9*numerator i := by sorry
