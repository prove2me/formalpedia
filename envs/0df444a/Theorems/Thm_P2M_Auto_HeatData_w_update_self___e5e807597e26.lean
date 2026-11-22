-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_w_update_self___e5e807597e26
-- name    : P2M_Auto_HeatData_w_update_self___e5e807597e26
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:53.17896+00:00
-- url     : https://prove2.me/theorems/c89619c7-058d-4ea5-8bb7-2a0f501ffdc4
-- title:
--   P2 M Auto Heat Data w update self   e5e807597e26: P2 M Auto Heat Data w update self   e5e807597e26
-- statement:
--   The P2 M Auto Heat Data w update self   e5e807597e26 construction uses the P2 M Auto Heat Data w update self   e5e807597e26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3208-L3210
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3208-L3210

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
omit [Fintype ι] [DecidableEq ι]

theorem P2M_Auto_HeatData_w_update_self___e5e807597e26 (v : Fin 3) (τ : ℝ) :
    Hd.w p (Function.update σ v τ) v = gweight Hd.u Hd.h τ (p v) := by sorry

alias «Auto».«HeatData».«w_update_self_σ» := P2M_Auto_HeatData_w_update_self___e5e807597e26
