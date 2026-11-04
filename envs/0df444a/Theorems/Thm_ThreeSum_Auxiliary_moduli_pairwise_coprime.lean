-- Prove2me | Theorems.Thm_ThreeSum_Auxiliary_moduli_pairwise_coprime
-- name    : ThreeSum.Auxiliary.moduli_pairwise_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:29.504724+00:00
-- url     : https://prove2.me/theorems/3c0802ce-7d45-47c8-b397-792992350a59
-- title:
--   Auxiliary: moduli pairwise coprime
-- statement:
--   The Auxiliary construction uses the moduli pairwise coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L42-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L42-L49

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators

theorem ThreeSum.Auxiliary.moduli_pairwise_coprime (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    (moduli C : Set ℤ).Pairwise (fun a b => IsCoprime a b) := by sorry
