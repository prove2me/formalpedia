-- Prove2me | Theorems.Thm_ThreeSum_Scales_actual_auxiliary_cardinality
-- name    : ThreeSum.Scales.actual_auxiliary_cardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:57.886205+00:00
-- url     : https://prove2.me/theorems/03d8024a-62a0-46a4-a028-e83063ea4f2a
-- title:
--   Scales: actual auxiliary cardinality
-- statement:
--   The Scales construction uses the actual auxiliary cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L899-L903
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L899-L903

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.Scales.actual_auxiliary_cardinality (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, Nat.log2 (3 * n ^ k) < candidateCount n := by sorry
