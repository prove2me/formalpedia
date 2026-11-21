-- Prove2me | Theorems.Thm_QuantumInfo_Channel_apply_trace
-- name    : QuantumInfo.Channel.apply_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:54.51718+00:00
-- url     : https://prove2.me/theorems/f31108ec-8b68-4e3a-bd2b-68dd1fe150ae
-- title:
--   Channel: apply trace
-- statement:
--   **Trace preservation.** `Tr(Φ ρ) = Tr ρ` — the defining TP property, from
--   `∑ᵢ Kᵢᴴ Kᵢ = 1` and trace cyclicity.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L79-L83
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L79-L83

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

theorem QuantumInfo.Channel.apply_trace (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.apply ρ).trace = ρ.trace := by sorry
