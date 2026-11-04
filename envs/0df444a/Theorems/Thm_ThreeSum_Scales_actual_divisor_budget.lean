-- Prove2me | Theorems.Thm_ThreeSum_Scales_actual_divisor_budget
-- name    : ThreeSum.Scales.actual_divisor_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:42.218171+00:00
-- url     : https://prove2.me/theorems/0ccbe6ba-ca59-4859-8a21-61de5f9d60bc
-- title:
--   Scales: actual divisor budget
-- statement:
--   The Scales construction uses the actual divisor budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L669-L700
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L669-L700

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

theorem ThreeSum.Scales.actual_divisor_budget (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      divisorBudget k n * primeWindow n ≤
        (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)) := by sorry
