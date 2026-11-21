-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_posSemidef
-- name    : QuantumInfo.Channel.apply_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:58.829209+00:00
-- url     : https://prove2.me/theorems/f9ed1eef-b978-460e-af5e-98ff63d2a89b
-- title:
--   Channel: apply pos Semidef
-- statement:
--   **Positivity.** A channel maps positive-semidefinite operators to positive-semidefinite
--   operators: each `Kᵢ ρ Kᵢᴴ` is PSD, and PSD is closed under finite sums.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L87-L92
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L87-L92

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

theorem QuantumInfo.Channel.apply_posSemidef (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (Φ.apply ρ).PosSemidef := by sorry
