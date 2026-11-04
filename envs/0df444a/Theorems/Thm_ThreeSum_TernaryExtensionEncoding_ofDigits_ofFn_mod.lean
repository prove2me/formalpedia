-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_ofDigits_ofFn_mod
-- name    : ThreeSum.TernaryExtensionEncoding.ofDigits_ofFn_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:31.111273+00:00
-- url     : https://prove2.me/theorems/90b389ef-6915-462d-8f5b-954aa197b028
-- title:
--   Ternary Extension Encoding: of Digits of Fn mod
-- statement:
--   The Ternary Extension Encoding construction uses the of Digits of Fn mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L92-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L92-L96

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

theorem ThreeSum.TernaryExtensionEncoding.ofDigits_ofFn_mod {d : ℕ} (hd : 0<d) (a : Fin d → ℕ) :
    Nat.ofDigits p (List.ofFn a)%p=a ⟨0,hd⟩%p := by sorry
