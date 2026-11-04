-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_remainderRelation_exists
-- name    : ThreeSum.TernaryExtensionEncoding.remainderRelation_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:54.928194+00:00
-- url     : https://prove2.me/theorems/67455dfe-8b9c-45d2-bd75-a22049a2971f
-- title:
--   Ternary Extension Encoding: remainder Relation exists
-- statement:
--   The Ternary Extension Encoding construction uses the remainder Relation exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L81-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L81-L101

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.remainderRelation_exists {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) (a b : Fin f.natDegree → ZMod p) :
    ∃ h r : Fin f.natDegree → ZMod p, remainderRelation a b h r := by sorry
