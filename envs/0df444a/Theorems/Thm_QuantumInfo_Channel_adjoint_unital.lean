-- Prove2me | Theorems.Thm_QuantumInfo_Channel_adjoint_unital
-- name    : QuantumInfo.Channel.adjoint_unital
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:57.089672+00:00
-- url     : https://prove2.me/theorems/de8edd25-02bb-4a73-800c-1621366491e0
-- title:
--   Channel: adjoint unital
-- statement:
--   **The adjoint is unital:** `Φ† 1 = 1`, directly from the TP constraint `∑ᵢ Kᵢᴴ Kᵢ = 1`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L123-L126
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L123-L126

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

theorem QuantumInfo.Channel.adjoint_unital [DecidableEq m] (Φ : Channel n m ι) : Φ.adjoint 1 = 1 := by sorry
