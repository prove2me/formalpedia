-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_selectPrime_min
-- name    : ThreeSum.PrimeChain.selectPrime_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:35.170005+00:00
-- url     : https://prove2.me/theorems/3a76ee09-302b-47ce-a917-111b978f4322
-- title:
--   Prime Chain: select Prime min
-- statement:
--   The Prime Chain construction uses the select Prime min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L125-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L125-L135

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}

theorem ThreeSum.PrimeChain.selectPrime_min (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) (q : ℕ) {p : ℕ} (hp : p ∈ candidates) :
    score T difference weight (q * selectPrime candidates T difference weight q) ≤
      score T difference weight (q * p) := by sorry
