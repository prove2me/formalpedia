-- Prove2me | Theorems.Thm_ThreeSum_Auxiliary_separates_nonzero
-- name    : ThreeSum.Auxiliary.separates_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:09.160249+00:00
-- url     : https://prove2.me/theorems/467abfd1-ad8b-447e-a433-1408581b96f0
-- title:
--   Auxiliary: separates nonzero
-- statement:
--   The Auxiliary construction uses the separates nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L51-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L51-L58

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators

theorem ThreeSum.Auxiliary.separates_nonzero (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    {M : ℕ} (hprod : M < ∏ p ∈ C, p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli C, ¬p ∣ z := by sorry
