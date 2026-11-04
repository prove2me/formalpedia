-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_word_mono
-- name    : ThreeSum.LightExtensionQuotientSearch.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:16.630699+00:00
-- url     : https://prove2.me/theorems/1d81df78-f1ab-4d4e-bcf5-b1b520027f3c
-- title:
--   Light Extension Quotient Search: word mono
-- statement:
--   The Light Extension Quotient Search construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean#L27-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean#L27-L30

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_word_mono

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionQuotientSearch._p2m_local_instance_7afa0e64b3_11

theorem ThreeSum.LightExtensionQuotientSearch.word_mono (dim p u v q : ℕ) (hu : u≤q) (hv : v≤q) :
    LightExtensionQuotientPredicate.word dim p u v ≤ LightExtensionQuotientPredicate.word dim p q q := by sorry
