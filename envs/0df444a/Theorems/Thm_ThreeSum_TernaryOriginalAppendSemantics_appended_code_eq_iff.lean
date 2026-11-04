-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalAppendSemantics_appended_code_eq_iff
-- name    : ThreeSum.TernaryOriginalAppendSemantics.appended_code_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:08.606992+00:00
-- url     : https://prove2.me/theorems/0cb8dd33-7083-40f7-9f56-3116935f39bb
-- title:
--   Ternary Original Append Semantics: appended code eq iff
-- statement:
--   The Ternary Original Append Semantics construction uses the appended code eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L48-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L48-L56

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalAppendSemantics
open Finset TernaryOriginalRowMenu TernaryExtensionEncoding
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryOriginalAppendSemantics.appended_code_eq_iff {r : ℕ} (a b : Fin r→ZMod p) (x y : ZMod p) :
    coefficientCode (appendVector a x)=coefficientCode (appendVector b y) ↔ a=b ∧ x=y := by sorry
