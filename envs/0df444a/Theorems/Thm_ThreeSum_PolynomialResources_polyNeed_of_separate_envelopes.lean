-- Prove2me | Theorems.Thm_ThreeSum_PolynomialResources_polyNeed_of_separate_envelopes
-- name    : ThreeSum.PolynomialResources.polyNeed_of_separate_envelopes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:48.581849+00:00
-- url     : https://prove2.me/theorems/e26c646c-9afb-4c0a-ba4a-a9db42934d5b
-- title:
--   Polynomial Resources: poly Need of separate envelopes
-- statement:
--   The Polynomial Resources construction uses the poly Need of separate envelopes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L71-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PolynomialResources.lean#L71-L84

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
open ThreeSum ThreeSum.PolynomialResources
open StageBounds Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.PolynomialResources.polyNeed_of_separate_envelopes {need : ℕ → ℕ → Light.Need}
    {fw fc fd : ℕ → ℕ} {aw ac ad : ℝ}
    (hw : PowerBound fw aw) (hc : PowerBound fc ac) (hd : PowerBound fd ad)
    (ew ec ed : ℕ)
    (hword : ∀ n U, (need n U).word ≤ fw n*(U+1)^ew)
    (hcells : ∀ n U, (need n U).cells ≤ fc n*(U+1)^ec)
    (hdepth : ∀ n U, (need n U).depth ≤ fd n*(U+1)^ed) : Light.PolyNeed need := by sorry
