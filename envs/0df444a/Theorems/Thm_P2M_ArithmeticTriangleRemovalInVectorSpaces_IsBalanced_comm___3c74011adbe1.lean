-- Prove2me | Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___3c74011adbe1
-- name    : P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___3c74011adbe1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:35.309826+00:00
-- url     : https://prove2.me/theorems/e79f61bc-c4df-4a88-9ee9-c0bc9759b129
-- title:
--   P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   3c74011adbe1: P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   3c74011adbe1
-- statement:
--   The P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   3c74011adbe1 construction uses the P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   3c74011adbe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean#L212-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean#L212-L216

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}

theorem P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___3c74011adbe1 (hb : IsBalanced N w₁ w₂ w₃) : IsBalanced N w₃ w₂ w₁ := by sorry

alias «ArithmeticTriangleRemovalInVectorSpaces».«IsBalanced».«comm₁₃» := P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___3c74011adbe1
