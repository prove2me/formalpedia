-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_encode_digit
-- name    : ThreeSum.TernaryExtensionEncoding.encode_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:55.595879+00:00
-- url     : https://prove2.me/theorems/039b3cf9-4a68-41c8-98ec-771a115137dd
-- title:
--   Ternary Extension Encoding: encode digit
-- statement:
--   The Ternary Extension Encoding construction uses the encode digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L11-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L11-L23

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.encode_digit {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f)
    (i : Fin f.natDegree) :
    encode hf x/p^i.val%p=((coefficients hf) x i).val := by sorry
