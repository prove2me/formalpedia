-- Prove2me | Theorems.Thm_ThreeSum_PolynomialResources_natural_polynomial_of_powerBound
-- name    : ThreeSum.PolynomialResources.natural_polynomial_of_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:22.952139+00:00
-- url     : https://prove2.me/theorems/0bb8a5ec-006e-4096-8ffe-d25f5566eeaf
-- title:
--   Polynomial Resources: natural polynomial of power Bound
-- statement:
--   The Polynomial Resources construction uses the natural polynomial of power Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L21-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L21-L40

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.PolynomialResources.natural_polynomial_of_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    ∃ C k : ℕ, ∀ n : ℕ, f n ≤ C*(n+1)^k := by sorry
