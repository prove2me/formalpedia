-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_coefficients_mk_vector
-- name    : ThreeSum.TernaryExtensionEncoding.coefficients_mk_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:24.517827+00:00
-- url     : https://prove2.me/theorems/ebbb4345-bdc2-4fd2-978e-dfa22f55f36f
-- title:
--   Ternary Extension Encoding: coefficients mk vector
-- statement:
--   The Ternary Extension Encoding construction uses the coefficients mk vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L46-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L46-L53

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.coefficients_mk_vector {f : (ZMod p)[X]} (hf : f.Monic)
    (a : Fin f.natDegree → ZMod p) :
    coefficients hf (AdjoinRoot.mk f (vectorPolynomial a))=a := by sorry
