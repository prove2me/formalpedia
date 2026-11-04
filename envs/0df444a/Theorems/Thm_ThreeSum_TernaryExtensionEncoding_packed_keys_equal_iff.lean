-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_packed_keys_equal_iff
-- name    : ThreeSum.TernaryExtensionEncoding.packed_keys_equal_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:55.239739+00:00
-- url     : https://prove2.me/theorems/dc6cf98b-ff85-45b5-9804-1eb5333254fb
-- title:
--   Ternary Extension Encoding: packed keys equal iff
-- statement:
--   The Ternary Extension Encoding construction uses the packed keys equal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L21-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L21-L23

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

theorem ThreeSum.TernaryExtensionEncoding.packed_keys_equal_iff {r : ℕ} (a b : Fin r → ZMod p) :
    coefficientCode a=coefficientCode b ↔ a=b := by sorry
