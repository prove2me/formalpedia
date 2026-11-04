-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_bucket_product_eq_sum
-- name    : ThreeSum.RawIncidences.bucket_product_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:59.979833+00:00
-- url     : https://prove2.me/theorems/a0b32eff-bf82-4b92-b287-b89649585a68
-- title:
--   Raw Incidences: bucket product eq sum
-- statement:
--   The Raw Incidences construction uses the bucket product eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L347-L361
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L347-L361

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.RawIncidences.bucket_product_eq_sum {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ∑ j ∈ B, ∑ k ∈ C,
        if globalModulus h J ∣ b j % P - tupleLeft t ∧
          globalModulus h J ∣ c k % P + d - tupleRight t then 1 else 0 := by sorry
