-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalAppendSemantics_physical_hash
-- name    : ThreeSum.TernaryOriginalAppendSemantics.physical_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:58.656025+00:00
-- url     : https://prove2.me/theorems/0993d62a-ec60-4725-9d00-e7cbabe0a433
-- title:
--   Ternary Original Append Semantics: physical hash
-- statement:
--   The Ternary Original Append Semantics construction uses the physical hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L12-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean#L12-L35

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

theorem ThreeSum.TernaryOriginalAppendSemantics.physical_hash (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (J : ℕ)
    (raw : Fin (J+2)→ℤ) (z : ℕ→ℤ) (c : ℕ→ℕ)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=(seedRow (J+2) ℓ seed (digitOrder J i)).val) :
    LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) ℓ seed (fun i => (raw i : ZMod p))).val := by sorry
