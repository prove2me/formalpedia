-- Prove2me | Theorems.Thm_ThreeSum_PrimeDensity_eventually_lower_count
-- name    : ThreeSum.PrimeDensity.eventually_lower_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:36.759972+00:00
-- url     : https://prove2.me/theorems/58922a08-1c8f-43b2-8d55-c082cf20ca36
-- title:
--   Prime Density: eventually lower count
-- statement:
--   The Prime Density construction uses the eventually lower count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeDensity.lean#L72-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PrimeDensity.lean#L72-L85

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity
set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section

theorem ThreeSum.PrimeDensity.eventually_lower_count :
    ∀ᶠ y : ℕ in atTop, (2 : ℝ) * ((y : ℝ) / Real.log y) ≤ Nat.primeCounting (4 * y) := by sorry
