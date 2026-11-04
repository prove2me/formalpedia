-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_codeDigits_lt
-- name    : ThreeSum.TernaryExtensionEncoding.codeDigits_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:50.212017+00:00
-- url     : https://prove2.me/theorems/11c27897-eb5c-4a44-88f1-de8fb47e9802
-- title:
--   Ternary Extension Encoding: code Digits lt
-- statement:
--   The Ternary Extension Encoding construction uses the code Digits lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L13-L14
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L13-L14

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.codeDigits_lt (code k : ℕ) : codeDigits (p := p) code k<p := by sorry
