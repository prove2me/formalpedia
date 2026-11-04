-- Prove2me | Theorems.Thm_ThreeSum_Scales_modulus_eventually_ge_radix_div_power
-- name    : ThreeSum.Scales.modulus_eventually_ge_radix_div_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:55.824886+00:00
-- url     : https://prove2.me/theorems/b7d6d721-f3c9-425e-8568-ab262de23066
-- title:
--   Scales: modulus eventually ge radix div power
-- statement:
--   The Scales construction uses the modulus eventually ge radix div power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L631-L642
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L631-L642

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

theorem ThreeSum.Scales.modulus_eventually_ge_radix_div_power {P : ℕ → ℕ}
    (hP : ∀ᶠ n : ℕ in atTop, primeWindow n ^ primeDepth radix n ≤ P n)
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (radix n : ℝ) / (n : ℝ) ^ d ≤ P n := by sorry
