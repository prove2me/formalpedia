-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_leftWeights_cardinality
-- name    : ThreeSum.BlockEncoding.leftWeights_cardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:51.829021+00:00
-- url     : https://prove2.me/theorems/172b0577-84c3-41ee-8888-1e6f07fade70
-- title:
--   Block Encoding: left Weights cardinality
-- statement:
--   The Block Encoding construction uses the left Weights cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L206-L212
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L206-L212

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.BlockEncoding.leftWeights_cardinality {h J : ℕ} (o : Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (Coord J (512 * h)))
    (hS : (leftWeights o P B b S : ℤ) ≠ 0) : S.card = J * h := by sorry
