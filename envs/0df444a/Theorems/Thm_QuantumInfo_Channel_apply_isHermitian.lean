-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_isHermitian
-- name    : QuantumInfo.Channel.apply_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:56.555202+00:00
-- url     : https://prove2.me/theorems/21812f06-d257-4933-9e96-477aa5656889
-- title:
--   Channel: apply is Hermitian
-- statement:
--   A channel preserves Hermiticity.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L95-L101
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L95-L101

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

theorem QuantumInfo.Channel.apply_isHermitian (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (Φ.apply ρ).IsHermitian := by sorry
