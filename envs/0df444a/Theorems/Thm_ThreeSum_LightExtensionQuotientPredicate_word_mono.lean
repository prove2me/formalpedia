-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_word_mono
-- name    : ThreeSum.LightExtensionQuotientPredicate.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:26.755571+00:00
-- url     : https://prove2.me/theorems/cd2aceb7-08a3-4fea-99d3-7506e3a33660
-- title:
--   Light Extension Quotient Predicate: word mono
-- statement:
--   The Light Extension Quotient Predicate construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientPredicate.lean#L42-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientPredicate.lean#L42-L45

import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

theorem ThreeSum.LightExtensionQuotientPredicate.word_mono {d p u v U V : ℕ} (hu : u≤U) (hv : v≤V) :
    word d p u v≤word d p U V := by sorry
