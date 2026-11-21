-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_smul
-- name    : QuantumInfo.Channel.apply_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:56.055191+00:00
-- url     : https://prove2.me/theorems/685e6324-6069-4177-b6c5-caefd36f1613
-- title:
--   Channel: apply smul
-- statement:
--   The channel action commutes with scalar multiplication.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L73-L75
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L73-L75

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

theorem QuantumInfo.Channel.apply_smul (Φ : Channel n m ι) (c : ℂ) (ρ : Matrix n n ℂ) :
    Φ.apply (c • ρ) = c • Φ.apply ρ := by sorry
