-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_of_natDegree_lt
-- name    : ThreeSum.TernaryExtensionEncoding.vectorPolynomial_of_natDegree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:37.044244+00:00
-- url     : https://prove2.me/theorems/0684f61b-7469-4e68-8d21-a6f65269e464
-- title:
--   Ternary Extension Encoding: vector Polynomial of nat Degree lt
-- statement:
--   The Ternary Extension Encoding construction uses the vector Polynomial of nat Degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L55-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L55-L63

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.vectorPolynomial_of_natDegree_lt {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.natDegree<d) : vectorPolynomial (fun i : Fin d => f.coeff i.val)=f := by sorry
