-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCosts_time_eventually_uniform
-- name    : ThreeSum.TernaryHybridCosts.time_eventually_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:55.131195+00:00
-- url     : https://prove2.me/theorems/66792cd9-a276-4ad5-abb6-700b3e927760
-- title:
--   Ternary Hybrid Costs: time eventually uniform
-- statement:
--   A single eventual size threshold bounds every admissible natural U.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean#L35-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean#L35-L43

import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCosts
open Light StageBounds Filter
noncomputable section

theorem ThreeSum.TernaryHybridCosts.time_eventually_uniform {T : ℕ → ℕ} {a b : ℝ}
    (hT : PowerBound T a) (ha : 0 ≤ a) (hab : a < b) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, U ≤ n^κ →
      (TernaryHybridCore.time T κ cutoff n U : ℝ) ≤ (n : ℝ)^b := by sorry
