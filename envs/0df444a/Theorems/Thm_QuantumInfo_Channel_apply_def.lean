-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_def
-- name    : QuantumInfo.Channel.apply_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:59.665915+00:00
-- url     : https://prove2.me/theorems/04ffd67b-fd18-4c0d-9ff8-9cface3d6056
-- title:
--   Channel: apply def
-- statement:
--   The channel action, unfolded to its Kraus sum. **Not `@[simp]`**: as a head unfolder it would
--   rewrite every `Φ.apply ρ` before more specific closed forms such as `id_apply` could fire. Use it
--   explicitly when the sum is what you want.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L64-L65
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L64-L65

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

theorem QuantumInfo.Channel.apply_def (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    Φ.apply ρ = ∑ i : ι, Φ.kraus i * ρ * (Φ.kraus i)ᴴ := by sorry
