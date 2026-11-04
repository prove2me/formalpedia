-- Prove2me | Theorems.Thm_ThreeSum_PolynomialResources_polyBound_of_powerBound
-- name    : ThreeSum.PolynomialResources.polyBound_of_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:36.618206+00:00
-- url     : https://prove2.me/theorems/86460bf8-1fb0-4374-b9cc-444140f1f5ca
-- title:
--   Polynomial Resources: poly Bound of power Bound
-- statement:
--   The Polynomial Resources construction uses the poly Bound of power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L42-L46

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.PolynomialResources.polyBound_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ s k : ℕ, ∀ n : ℕ, f n ≤ Light.polyBound s k [n] := by sorry
