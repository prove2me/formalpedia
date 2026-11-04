-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_exists_monic_irreducible
-- name    : ThreeSum.TernaryExtensionEncoding.exists_monic_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:26.87384+00:00
-- url     : https://prove2.me/theorems/b0723669-8aed-402c-9285-cd9889d4f74f
-- title:
--   Ternary Extension Encoding: exists monic irreducible
-- statement:
--   The Ternary Extension Encoding construction uses the exists monic irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L23-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionEncoding.lean#L23-L30

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

theorem ThreeSum.TernaryExtensionEncoding.exists_monic_irreducible (d : ℕ) (hd : 0<d) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree=d := by sorry
