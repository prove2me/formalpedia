-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_add
-- name    : QuantumInfo.Channel.apply_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:57.702091+00:00
-- url     : https://prove2.me/theorems/1db68a8b-8e7b-41ca-931f-257f09e3183e
-- title:
--   Channel: apply add
-- statement:
--   The channel action is additive.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L68-L70
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L68-L70

module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
set_option autoImplicit false
@[expose] public section
public section
open Matrix
open scoped ComplexOrder
open QuantumInfo
open QuantumInfo.Channel
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n]

theorem QuantumInfo.Channel.apply_add (Φ : Channel n m ι) (ρ σ : Matrix n n ℂ) :
    Φ.apply (ρ + σ) = Φ.apply ρ + Φ.apply σ := by sorry
