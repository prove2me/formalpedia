-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostSuffixValueBounds_abs_value_le_card
-- name    : ThreeSum.ReportingHostSuffixValueBounds.abs_value_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:36.61212+00:00
-- url     : https://prove2.me/theorems/8cee0c57-76d4-403e-932a-d43d57b3c535
-- title:
--   Reporting Host Suffix Value Bounds: abs value le card
-- statement:
--   The Reporting Host Suffix Value Bounds construction uses the abs value le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixValueBounds.lean#L14-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostSuffixValueBounds.lean#L14-L32

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixValueBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixValueBounds
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
open scoped BigOperators

theorem ThreeSum.ReportingHostSuffixValueBounds.abs_value_le_card {W cut stage B D : ℕ} (f g : Finset (Fin W) → ℤ)
    (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D) :
    |ReportingHostQueryBounds.value f g stage preL preR Q| ≤
      ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by sorry
