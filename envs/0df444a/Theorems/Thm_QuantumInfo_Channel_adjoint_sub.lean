-- Prove2me | Theorems.Thm_QuantumInfo_Channel_adjoint_sub
-- name    : QuantumInfo.Channel.adjoint_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:47:02.970629+00:00
-- url     : https://prove2.me/theorems/aa8135d9-806c-479b-8282-021952ecbc2b
-- title:
--   Channel: adjoint sub
-- statement:
--   The adjoint is **subtractive** (linearity in `P`).
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L138-L140
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L138-L140

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

theorem QuantumInfo.Channel.adjoint_sub (Φ : Channel n m ι) (P Q : Matrix m m ℂ) :
    Φ.adjoint (P - Q) = Φ.adjoint P - Φ.adjoint Q := by sorry
