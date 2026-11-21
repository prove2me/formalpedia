-- Prove2me | Theorems.Thm_QuantumInfo_Channel_adjoint_trace_mul
-- name    : QuantumInfo.Channel.adjoint_trace_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:47:28.101452+00:00
-- url     : https://prove2.me/theorems/dbb0e7f8-818d-4e9c-9c35-65c1a660a6df
-- title:
--   Channel: adjoint trace mul
-- statement:
--   **Adjoint (trace) duality:** `Tr(P · Φ ρ) = Tr(Φ† P · ρ)`. The defining property of the
--   adjoint, via trace cyclicity rotating `Kᵢᴴ` to the front of each summand.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L157-L166
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L157-L166

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

theorem QuantumInfo.Channel.adjoint_trace_mul (Φ : Channel n m ι) (P : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    (P * Φ.apply ρ).trace = (Φ.adjoint P * ρ).trace := by sorry
