-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTrimming_heavyEvent_markov
-- name    : ThreeSum.TernaryCoverTrimming.heavyEvent_markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:45:26.291201+00:00
-- url     : https://prove2.me/theorems/bc9224f6-f79a-4db5-9e00-6897612dd120
-- title:
--   Ternary Cover Trimming: heavy Event markov
-- statement:
--   The Ternary Cover Trimming construction uses the heavy Event markov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L118-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L118-L128

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverTrimming.heavyEvent_markov (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) (B : ℕ) :
    B * (heavyEvent event vertices vector a B).card ≤
      loadedMass event vertices vector a := by sorry
