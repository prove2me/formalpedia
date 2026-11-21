-- Prove2me | Theorems.Thm_QuantumInfo_Channel_adjoint_le_one
-- name    : QuantumInfo.Channel.adjoint_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:47:22.425204+00:00
-- url     : https://prove2.me/theorems/3cdd8b03-44db-4068-bc80-414c2ec9ac86
-- title:
--   Channel: adjoint le one
-- statement:
--   **`0 ≤ P ≤ I ⟹ 0 ≤ Φ† P ≤ I`** (the upper half): unitality +
--   subtractivity give `1 − Φ† P = Φ† (1 − P)`, PSD by `adjoint_posSemidef`.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L149-L153
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L149-L153

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

theorem QuantumInfo.Channel.adjoint_le_one [DecidableEq m] (Φ : Channel n m ι) {P : Matrix m m ℂ}
    (_hP : P.PosSemidef) (hP' : ((1 : Matrix m m ℂ) - P).PosSemidef) :
    ((1 : Matrix n n ℂ) - Φ.adjoint P).PosSemidef := by sorry
