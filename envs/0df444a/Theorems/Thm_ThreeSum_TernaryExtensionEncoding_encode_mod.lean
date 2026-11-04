-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_encode_mod
-- name    : ThreeSum.TernaryExtensionEncoding.encode_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:32.019202+00:00
-- url     : https://prove2.me/theorems/6d25243b-a150-42f4-b1eb-47a5bbfae94d
-- title:
--   Ternary Extension Encoding: encode mod
-- statement:
--   The Ternary Extension Encoding construction uses the encode mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L98-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L98-L102

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
set_option maxHeartbeats 3000000
variable (p : ℕ) [Fact p.Prime]
variable {p}

theorem ThreeSum.TernaryExtensionEncoding.encode_mod {f : (ZMod p)[X]} (hf : f.Monic) (hd : 0<f.natDegree)
    (x : AdjoinRoot f) : encode hf x%p=(constantCoefficient hf hd x).val := by sorry
