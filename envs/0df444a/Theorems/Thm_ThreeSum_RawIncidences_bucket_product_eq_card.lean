-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_bucket_product_eq_card
-- name    : ThreeSum.RawIncidences.bucket_product_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:51.840619+00:00
-- url     : https://prove2.me/theorems/ada61d14-b604-401b-bbc1-506f62df6236
-- title:
--   Raw Incidences: bucket product eq card
-- statement:
--   The Raw Incidences construction uses the bucket product eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L363-L369
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L363-L369

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

theorem ThreeSum.RawIncidences.bucket_product_eq_card {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ((B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
        globalModulus h J ∣ c p.2 % P + d - tupleRight t).card := by sorry
