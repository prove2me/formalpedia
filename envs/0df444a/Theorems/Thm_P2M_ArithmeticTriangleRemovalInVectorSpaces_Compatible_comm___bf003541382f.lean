-- Prove2me | Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f
-- name    : P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:16.994823+00:00
-- url     : https://prove2.me/theorems/e936faaf-a592-4673-9f00-04519eb957ab
-- title:
--   P2 M Arithmetic Triangle Removal In Vector Spaces Compatible comm   bf003541382f: P2 M Arithmetic Triangle Removal In Vector Spaces Compatible comm   bf003541382f
-- statement:
--   The P2 M Arithmetic Triangle Removal In Vector Spaces Compatible comm   bf003541382f construction uses the P2 M Arithmetic Triangle Removal In Vector Spaces Compatible comm   bf003541382f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L113-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L113-L114

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}

theorem P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f (h : Compatible N π₁ π₂ π₃) : Compatible N π₃ π₂ π₁ := by sorry

alias «ArithmeticTriangleRemovalInVectorSpaces».«Compatible».«comm₁₃» := P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f
