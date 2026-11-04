-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_append_original_key
-- name    : ThreeSum.TernaryExtensionEncoding.append_original_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:16.630993+00:00
-- url     : https://prove2.me/theorems/760064a6-5f8b-4c4d-8863-6ddc828ff494
-- title:
--   Ternary Extension Encoding: append original key
-- statement:
--   The Ternary Extension Encoding construction uses the append original key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L68-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean#L68-L82

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

theorem ThreeSum.TernaryExtensionEncoding.append_original_key (hf : f.Monic) (hd : 0<f.natDegree) {r J : ℕ}
    (x y : AdjoinRoot f) (raw : Fin (J+2) → ℤ) (z : ℕ → ℤ) (c : ℕ → ℕ)
    (previous : Fin r → ZMod p)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i)).val) :
    LightTernaryAppendKeys.key p (p^r) (J+2) (fun _ => coefficientCode previous)
      (fun _ => z) c 0=
      coefficientCode (appendVector previous
        (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
          (fun i => (raw i : ZMod p)))) := by sorry
