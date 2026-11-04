-- Prove2me | Theorems.Thm_ThreeSum_PrimeChain_selectPrime_mem
-- name    : ThreeSum.PrimeChain.selectPrime_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:31.61271+00:00
-- url     : https://prove2.me/theorems/83dc6c94-409f-4ff9-8133-89bfa13d7d25
-- title:
--   Prime Chain: select Prime mem
-- statement:
--   The Prime Chain construction uses the select Prime mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L114-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeChain.lean#L114-L123

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

theorem ThreeSum.PrimeChain.selectPrime_mem (candidates : List ℕ) (hne : candidates ≠ [])
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (q : ℕ) :
    selectPrime candidates T difference weight q ∈ candidates := by sorry
