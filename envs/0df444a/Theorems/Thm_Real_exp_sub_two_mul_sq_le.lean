-- Prove2me | Theorems.Thm_Real_exp_sub_two_mul_sq_le
-- name    : Real.exp_sub_two_mul_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:20:19.696725+00:00
-- url     : https://prove2.me/theorems/b0c07191-4f98-4b82-8a1d-876e37723e16
-- title:
--   Real: exp sub two mul sq le
-- statement:
--   Pointwise exponential bound: `exp (a - 2a²) ≤ 1 + a` for `a ≥ -1/2`.
--
--   This is the elementary inequality behind the second-order determinant bound: it
--   follows from `1 + x ≤ exp x` applied to `x = 2a² - a`, since
--   `(1 + 2a² - a) * (1 + a) = 1 + a² (1 + 2a) ≥ 1` when `1 + 2a ≥ 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean#L55-L63
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean#L55-L63

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients
set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate

theorem Real.exp_sub_two_mul_sq_le {a : ℝ} (ha : -(1 / 2) ≤ a) :
    Real.exp (a - 2 * a ^ 2) ≤ 1 + a := by sorry
