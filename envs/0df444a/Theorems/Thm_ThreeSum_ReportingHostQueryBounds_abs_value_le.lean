-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostQueryBounds_abs_value_le
-- name    : ThreeSum.ReportingHostQueryBounds.abs_value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:06.052801+00:00
-- url     : https://prove2.me/theorems/c89a6f4a-ed02-4ac4-9037-cbd2bcec04a8
-- title:
--   Reporting Host Query Bounds: abs value le
-- statement:
--   The Reporting Host Query Bounds construction uses the abs value le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean#L15-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean#L15-L36

import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Theorems.Thm_ThreeSum_SignedLeaf_abs_value_le

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostQueryBounds
open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ReportingHostQueryBounds.abs_value_le {W cut stage B D : ℕ} (f g : Finset (Fin W) → ℤ)
    (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D) :
    |value f g stage preL preR Q| ≤ ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by sorry
