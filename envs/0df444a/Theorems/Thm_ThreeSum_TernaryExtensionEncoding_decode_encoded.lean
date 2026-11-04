-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_encoded
-- name    : ThreeSum.TernaryExtensionEncoding.decode_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:25.06344+00:00
-- url     : https://prove2.me/theorems/ac55e47a-ed2f-4cd4-9031-ecfda045e1fd
-- title:
--   Ternary Extension Encoding: decode encoded
-- statement:
--   The Ternary Extension Encoding construction uses the decode encoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L25-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L25-L30

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.decode_encoded {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    (fun i : Fin f.natDegree => ((encode hf x/p^i.val%p : ℕ) : ZMod p))=
      coefficients hf x := by sorry
