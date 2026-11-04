-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostQueryBounds_boxStored_of_on
-- name    : ThreeSum.ReportingHostQueryBounds.boxStored_of_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:24.287159+00:00
-- url     : https://prove2.me/theorems/c8fe69c0-7cc5-418b-89fe-f4ed87ae4fc3
-- title:
--   Reporting Host Query Bounds: box Stored of on
-- statement:
--   The Reporting Host Query Bounds construction uses the box Stored of on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean#L52-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean#L52-L63

import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostQueryBounds
open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ReportingHostQueryBounds.boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*downsetCap W cut → μ' i = μ i) :
    LightBoxStages.StoredThrough μ' base cut f W := by sorry
