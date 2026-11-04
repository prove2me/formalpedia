-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_mk_decoded
-- name    : ThreeSum.TernaryExtensionEncoding.mk_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:06.776647+00:00
-- url     : https://prove2.me/theorems/7fbc6415-0e78-4422-aa8b-45b1cf189118
-- title:
--   Ternary Extension Encoding: mk decoded
-- statement:
--   The Ternary Extension Encoding construction uses the mk decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L32-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L32-L37

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.mk_decoded {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    AdjoinRoot.mk f (vectorPolynomial
      (fun i : Fin f.natDegree => ((encode hf x/p^i.val%p : ℕ) : ZMod p)))=x := by sorry
