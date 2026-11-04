-- Prove2me | Theorems.Thm_ThreeSum_Auxiliary_prime_product_lower
-- name    : ThreeSum.Auxiliary.prime_product_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:39.635996+00:00
-- url     : https://prove2.me/theorems/e1131f3e-94fc-4c7b-8980-3c6b44aefab1
-- title:
--   Auxiliary: prime product lower
-- statement:
--   The Auxiliary construction uses the prime product lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L24-L28

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators

theorem ThreeSum.Auxiliary.prime_product_lower (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    2 ^ C.card ≤ ∏ p ∈ C, p := by sorry
