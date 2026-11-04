-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_field_code
-- name    : ThreeSum.TernaryExtensionEncoding.decode_field_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:45.975196+00:00
-- url     : https://prove2.me/theorems/b20dcf97-53fe-45be-af25-720fb3d6a555
-- title:
--   Ternary Extension Encoding: decode field code
-- statement:
--   The Ternary Extension Encoding construction uses the decode field code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L45-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L45-L51

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.decode_field_code {f : (ZMod p)[X]} (hf : f.Monic) (code : Fin (p^f.natDegree)) :
    coefficients hf ((encodedEquiv hf).symm code)=coefficientVector f.natDegree code.val := by sorry
