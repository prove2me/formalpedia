-- Prove2me | Theorems.Thm_UlmsTheorem_UlmDifferentialRegression_ulm_44_zero
-- name    : UlmsTheorem.UlmDifferentialRegression.ulm_44_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:46.088653+00:00
-- url     : https://prove2.me/theorems/a6878f7a-221a-455e-bfcb-a59d05f9bfc7
-- title:
--   Ulm Differential Regression: ulm 44 zero
-- statement:
--   `f(0) = 0` for `Z/4 + Z/4`: its socle is exactly `2G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Regression.lean#L95-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Regression.lean#L95-L117

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

theorem UlmsTheorem.UlmDifferentialRegression.ulm_44_zero : ulmInvariant 2 (0 : Ordinal) (G := ZMod 4 × ZMod 4) = 0 := by sorry
