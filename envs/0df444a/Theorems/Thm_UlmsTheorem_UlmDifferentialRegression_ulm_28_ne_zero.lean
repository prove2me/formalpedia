-- Prove2me | Theorems.Thm_UlmsTheorem_UlmDifferentialRegression_ulm_28_ne_zero
-- name    : UlmsTheorem.UlmDifferentialRegression.ulm_28_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:53.570472+00:00
-- url     : https://prove2.me/theorems/0d31d071-0d3c-4d6b-8cbb-c73bb223024a
-- title:
--   Ulm Differential Regression: ulm 28 ne zero
-- statement:
--   `f(0) != 0` for `Z/2 + Z/8`: `(1,0)` is a socle element outside `2G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Regression.lean#L120-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Regression.lean#L120-L142

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Regression
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open UlmsTheorem.UlmDifferentialRegression
attribute [local instance] UlmsTheorem.UlmDifferentialRegression._p2m_local_instance_ed668a12d5_64

theorem UlmsTheorem.UlmDifferentialRegression.ulm_28_ne_zero : ulmInvariant 2 (0 : Ordinal) (G := ZMod 2 × ZMod 8) ≠ 0 := by sorry
