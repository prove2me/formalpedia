-- Prove2me | Theorems.Thm_QuantumInfo_Channel_id_apply
-- name    : QuantumInfo.Channel.id_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:46:54.021246+00:00
-- url     : https://prove2.me/theorems/0c3979ee-0787-4540-a286-9336dec23447
-- title:
--   Channel: id apply
-- statement:
--   The Channel construction uses the id apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L173-L175
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean#L173-L175

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

theorem QuantumInfo.Channel.id_apply (n : Type*) [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    (Channel.id n).apply ρ = ρ := by sorry
