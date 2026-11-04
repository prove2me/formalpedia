-- Prove2me | Theorems.Thm_ThreeSum_Auxiliary_product_gt_of_card
-- name    : ThreeSum.Auxiliary.product_gt_of_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:41.771954+00:00
-- url     : https://prove2.me/theorems/0f05db43-f29b-48d2-8fdb-74b8e13a8d7b
-- title:
--   Auxiliary: product gt of card
-- statement:
--   The Auxiliary construction uses the product gt of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L30-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Auxiliary.lean#L30-L33

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators

theorem ThreeSum.Auxiliary.product_gt_of_card (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (M : ℕ) (hcard : Nat.log 2 M < C.card) : M < ∏ p ∈ C, p := by sorry
