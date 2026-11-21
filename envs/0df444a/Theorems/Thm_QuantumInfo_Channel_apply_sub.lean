-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_sub
-- name    : QuantumInfo.Channel.apply_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:47:09.870576+00:00
-- url     : https://prove2.me/theorems/dd940619-9b93-49c6-bcfb-98c0693ec51a
-- title:
--   Channel: apply sub
-- statement:
--   The channel action is **subtractive** (linearity in the input).
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L104-L106
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L104-L106

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

theorem QuantumInfo.Channel.apply_sub (Φ : Channel n m ι) (ρ σ : Matrix n n ℂ) :
    Φ.apply (ρ - σ) = Φ.apply ρ - Φ.apply σ := by sorry
