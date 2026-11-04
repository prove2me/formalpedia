-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostQueryBounds_abs_value_le_word
-- name    : ThreeSum.ReportingHostQueryBounds.abs_value_le_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:52.231169+00:00
-- url     : https://prove2.me/theorems/a8023188-0ba2-4277-95bc-5ee4d06d3dd0
-- title:
--   Reporting Host Query Bounds: abs value le word
-- statement:
--   The Reporting Host Query Bounds construction uses the abs value le word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean#L38-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostQueryBounds.lean#L38-L50

import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostQueryBounds
open Light Finset ThreeSum.SubsetAddress
open scoped BigOperators

theorem ThreeSum.ReportingHostQueryBounds.abs_value_le_word {W cut stage t B D : ℕ} {lim : Limits}
    (f g : Finset (Fin W) → ℤ) (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hw : (LightSparseQuery.magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word) :
    |value f g stage preL preR Q| ≤ lim.word := by sorry
