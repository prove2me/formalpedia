-- Prove2me | Theorems.Thm_P2M_LieTrotter_hasDerivAt_exp_const_sub_smul__0b920a441cd3
-- name    : P2M_LieTrotter_hasDerivAt_exp_const_sub_smul__0b920a441cd3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:46:26.829981+00:00
-- url     : https://prove2.me/theorems/1b6cebb0-6945-489e-a887-fb36089191b5
-- title:
--   P2 M Lie Trotter has Deriv At exp const sub smul  0b920a441cd3: P2 M Lie Trotter has Deriv At exp const sub smul  0b920a441cd3
-- statement:
--   The derivative of `σ ↦ exp ((c − σ) • X)`, with `X` on the right.
--
--   Source: https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L63-L67
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean#L63-L67

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Definitions.Def_LieTrotter_Commutator
set_option autoImplicit false
@[expose] public section
public section
open NormedSpace Set
open LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
omit [NormOneClass 𝔸]

theorem P2M_LieTrotter_hasDerivAt_exp_const_sub_smul__0b920a441cd3 (X : 𝔸) (c σ : ℝ) :
    HasDerivAt (fun σ : ℝ => exp ((c - σ) • X)) (-(exp ((c - σ) • X) * X)) σ := by sorry

alias «LieTrotter».«hasDerivAt_exp_const_sub_smul'» := P2M_LieTrotter_hasDerivAt_exp_const_sub_smul__0b920a441cd3
