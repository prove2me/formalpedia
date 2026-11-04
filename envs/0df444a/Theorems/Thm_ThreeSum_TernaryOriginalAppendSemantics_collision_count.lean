-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalAppendSemantics_collision_count
-- name    : ThreeSum.TernaryOriginalAppendSemantics.collision_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:36.696932+00:00
-- url     : https://prove2.me/theorems/3ef36821-8b9e-40b8-9e02-dfee3a5f15b6
-- title:
--   Ternary Original Append Semantics: collision count
-- statement:
--   The Ternary Original Append Semantics construction uses the collision count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L58-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L58-L67

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalAppendSemantics
open Finset TernaryOriginalRowMenu TernaryExtensionEncoding
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryOriginalAppendSemantics.collision_count {B : Type*} [Fintype B] [DecidableEq B] {r Λ : ℕ}
    (ℓ : E→ₗ[ZMod p] ZMod p) (v : B→Fin Λ→ZMod p) (hash : B→Fin r→ZMod p) (seed : E×E) :
    (TernaryOriginalCollisions.collisionPairs (fun i => coefficientCode
      (appendVector (hash i) (TernaryOriginalRowMenu.row Λ ℓ seed (v i))))).card=
        TernaryOriginalCollisions.nextCollisions ℓ v hash seed := by sorry
