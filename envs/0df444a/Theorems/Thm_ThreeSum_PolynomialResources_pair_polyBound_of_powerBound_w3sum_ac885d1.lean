-- Prove2me | Theorems.Thm_ThreeSum_PolynomialResources_pair_polyBound_of_powerBound_w3sum_ac885d1
-- name    : ThreeSum.PolynomialResources.pair_polyBound_of_powerBound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:34.066746+00:00
-- url     : https://prove2.me/theorems/fee9c5b0-108a-4751-b17b-7c109c8cec45
-- title:
--   Polynomial Resources: pair poly Bound of power Bound
-- statement:
--   The Polynomial Resources construction uses the pair poly Bound of power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L48-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L48-L60

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.PolynomialResources.pair_polyBound_of_powerBound_w3sum_ac885d1 {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (e : ℕ) :
    ∃ s k : ℕ, ∀ n U : ℕ, f n*(U+1)^e ≤ Light.polyBound s k [n,U] := by sorry
