-- Prove2me | Theorems.Thm_QuantumInfo_Channel_adjoint_posSemidef
-- name    : QuantumInfo.Channel.adjoint_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:56.069925+00:00
-- url     : https://prove2.me/theorems/4a01d633-895e-4e69-b6b1-6df8408cad88
-- title:
--   Channel: adjoint pos Semidef
-- statement:
--   **The adjoint preserves positive-semidefiniteness:** each `Kᵢᴴ P Kᵢ` is PSD and PSD is
--   closed under finite sums.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L130-L135
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L130-L135

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

theorem QuantumInfo.Channel.adjoint_posSemidef (Φ : Channel n m ι) {P : Matrix m m ℂ} (hP : P.PosSemidef) :
    (Φ.adjoint P).PosSemidef := by sorry
