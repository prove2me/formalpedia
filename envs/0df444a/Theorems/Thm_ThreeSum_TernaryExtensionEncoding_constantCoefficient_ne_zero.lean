-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_constantCoefficient_ne_zero
-- name    : ThreeSum.TernaryExtensionEncoding.constantCoefficient_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:28.288089+00:00
-- url     : https://prove2.me/theorems/80f0242c-238f-4105-9cd7-c6bb402b0a2a
-- title:
--   Ternary Extension Encoding: constant Coefficient ne zero
-- statement:
--   The Ternary Extension Encoding construction uses the constant Coefficient ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L48-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L48-L53

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

theorem ThreeSum.TernaryExtensionEncoding.constantCoefficient_ne_zero {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) : constantCoefficient hf hd≠0 := by sorry
