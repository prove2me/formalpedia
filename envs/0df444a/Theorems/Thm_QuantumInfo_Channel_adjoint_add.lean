-- Prove2me | Theorems.Thm_QuantumInfo_Channel_adjoint_add
-- name    : QuantumInfo.Channel.adjoint_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:47:15.749726+00:00
-- url     : https://prove2.me/theorems/431a58c7-b00a-457f-ae12-ad54756a29ee
-- title:
--   Channel: adjoint add
-- statement:
--   The adjoint is **additive** (linearity in `P`).
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L143-L145
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L143-L145

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

theorem QuantumInfo.Channel.adjoint_add (Φ : Channel n m ι) (P Q : Matrix m m ℂ) :
    Φ.adjoint (P + Q) = Φ.adjoint P + Φ.adjoint Q := by sorry
