-- Prove2me | Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___927a6ae1263a
-- name    : P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___927a6ae1263a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:01.261314+00:00
-- url     : https://prove2.me/theorems/2fec0611-0536-4d27-9cd0-4720b5ff6c0d
-- title:
--   P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   927a6ae1263a: P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   927a6ae1263a
-- statement:
--   The P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   927a6ae1263a construction uses the P2 M Arithmetic Triangle Removal In Vector Spaces Is Balanced comm   927a6ae1263a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean#L208-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean#L208-L210

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___c955cfa1f590

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}

theorem P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___927a6ae1263a (hb : IsBalanced N w₁ w₂ w₃) : IsBalanced N w₁ w₃ w₂ := by sorry

alias «ArithmeticTriangleRemovalInVectorSpaces».«IsBalanced».«comm₂₃» := P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___927a6ae1263a
