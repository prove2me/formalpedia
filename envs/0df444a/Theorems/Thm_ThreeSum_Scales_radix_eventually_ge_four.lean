-- Prove2me | Theorems.Thm_ThreeSum_Scales_radix_eventually_ge_four
-- name    : ThreeSum.Scales.radix_eventually_ge_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:58.078163+00:00
-- url     : https://prove2.me/theorems/bb0cab72-e85a-45c7-9695-102b09e17aa0
-- title:
--   Scales: radix eventually ge four
-- statement:
--   The Scales construction uses the radix eventually ge four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L572-L576
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L572-L576

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

theorem ThreeSum.Scales.radix_eventually_ge_four : ∀ᶠ n : ℕ in atTop, 4 ≤ radix n := by sorry
