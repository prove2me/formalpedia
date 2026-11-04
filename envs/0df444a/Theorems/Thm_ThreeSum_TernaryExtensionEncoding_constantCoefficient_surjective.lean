-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_constantCoefficient_surjective
-- name    : ThreeSum.TernaryExtensionEncoding.constantCoefficient_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:27.126708+00:00
-- url     : https://prove2.me/theorems/fd67a8ec-3ac1-47fb-a591-dc6aba588d8e
-- title:
--   Ternary Extension Encoding: constant Coefficient surjective
-- statement:
--   The Ternary Extension Encoding construction uses the constant Coefficient surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L42-L46

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

theorem ThreeSum.TernaryExtensionEncoding.constantCoefficient_surjective {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) : Function.Surjective (constantCoefficient hf hd) := by sorry
