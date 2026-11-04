-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_remainderRelation_correct
-- name    : ThreeSum.TernaryExtensionEncoding.remainderRelation_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:39.331202+00:00
-- url     : https://prove2.me/theorems/f8e8e75f-c0d2-4a3e-8059-85d4afa3de22
-- title:
--   Ternary Extension Encoding: remainder Relation correct
-- statement:
--   The Ternary Extension Encoding construction uses the remainder Relation correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L69-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L69-L79

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.remainderRelation_correct {f : (ZMod p)[X]} (hf : f.Monic)
    (a b h r : Fin f.natDegree → ZMod p) (hr : remainderRelation a b h r) :
    coefficients hf ((coefficients hf).symm a*(coefficients hf).symm b)=r := by sorry
