-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_physical_original_hash
-- name    : ThreeSum.TernaryExtensionEncoding.physical_original_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:26.84342+00:00
-- url     : https://prove2.me/theorems/31dafa04-e7de-4540-b872-d6c364aa4835
-- title:
--   Ternary Extension Encoding: physical original hash
-- statement:
--   The Ternary Extension Encoding construction uses the physical original hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L37-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L37-L66

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
variable {f : (ZMod p)[X]} [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem ThreeSum.TernaryExtensionEncoding.physical_original_hash (hf : f.Monic) (hd : 0<f.natDegree) (J : ℕ)
    (x y : AdjoinRoot f) (raw : Fin (J+2) → ℤ) (z : ℕ → ℤ) (c : ℕ → ℕ)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i)).val) :
    LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p))).val := by sorry
