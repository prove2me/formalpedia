-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_coefficientCode_append
-- name    : ThreeSum.TernaryExtensionEncoding.coefficientCode_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:34:34.046891+00:00
-- url     : https://prove2.me/theorems/b0aa3820-4cfd-4b7c-bdb0-f050e22d73b5
-- title:
--   Ternary Extension Encoding: coefficient Code append
-- statement:
--   The Ternary Extension Encoding construction uses the coefficient Code append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L15-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L15-L19

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.coefficientCode_append {r : ℕ} (v : Fin r → ZMod p) (a : ZMod p) :
    coefficientCode (appendVector v a)=coefficientCode v+p^r*a.val := by sorry
