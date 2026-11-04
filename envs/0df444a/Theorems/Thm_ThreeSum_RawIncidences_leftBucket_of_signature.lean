-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_leftBucket_of_signature
-- name    : ThreeSum.RawIncidences.leftBucket_of_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:46.337881+00:00
-- url     : https://prove2.me/theorems/b9f87185-7779-44fa-b112-37935d234e8f
-- title:
--   Raw Incidences: left Bucket of signature
-- statement:
--   The Raw Incidences construction uses the left Bucket of signature property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L337-L340
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L337-L340

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

theorem ThreeSum.RawIncidences.leftBucket_of_signature {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {s t : ChoiceTuple h J} (he : leftSignature s = leftSignature t) :
    leftBucket P B b s = leftBucket P B b t := by sorry
