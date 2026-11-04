-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalAppendSemantics_append_key
-- name    : ThreeSum.TernaryOriginalAppendSemantics.append_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:16.383936+00:00
-- url     : https://prove2.me/theorems/6b1c8972-6067-4bf9-86c2-10e4323b3e93
-- title:
--   Ternary Original Append Semantics: append key
-- statement:
--   The Ternary Original Append Semantics construction uses the append key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L37-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L37-L46

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

theorem ThreeSum.TernaryOriginalAppendSemantics.append_key (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) {r J : ℕ}
    (raw : Fin (J+2)→ℤ) (z : ℕ→ℤ) (c : ℕ→ℕ) (previous : Fin r→ZMod p)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=(seedRow (J+2) ℓ seed (digitOrder J i)).val) :
    LightTernaryAppendKeys.key p (p^r) (J+2) (fun _ => coefficientCode previous) (fun _ => z) c 0=
      coefficientCode (appendVector previous (TernaryOriginalRowMenu.row (J+2) ℓ seed (fun i => (raw i : ZMod p)))) := by sorry
