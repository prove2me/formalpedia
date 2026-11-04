-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_time_mono
-- name    : ThreeSum.LightExtensionQuotientSearch.time_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:54.758577+00:00
-- url     : https://prove2.me/theorems/e81b0028-abf5-4cc7-8e1c-0fbe21a74001
-- title:
--   Light Extension Quotient Search: time mono
-- statement:
--   The Light Extension Quotient Search construction uses the time mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean#L20-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean#L20-L25

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_time_mono

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionQuotientSearch._p2m_local_instance_7afa0e64b3_11

theorem ThreeSum.LightExtensionQuotientSearch.time_mono (dim p u v q : ℕ) (hu : u≤q) (hv : v≤q) :
    LightExtensionQuotientPredicate.time dim p u v ≤ LightExtensionQuotientPredicate.time dim p q q := by sorry
