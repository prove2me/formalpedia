-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_Brow_update___289bec5b5b62
-- name    : P2M_Auto_HeatData_Brow_update___289bec5b5b62
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:33:06.458122+00:00
-- url     : https://prove2.me/theorems/b52b87e1-8548-4d54-a505-d3091cb350cf
-- title:
--   P2 M Auto Heat Data Brow update   289bec5b5b62: P2 M Auto Heat Data Brow update   289bec5b5b62
-- statement:
--   The P2 M Auto Heat Data Brow update   289bec5b5b62 construction uses the P2 M Auto Heat Data Brow update   289bec5b5b62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3226-L3228
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3226-L3228

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

theorem P2M_Auto_HeatData_Brow_update___289bec5b5b62 (v : Fin 3) (τ : ℝ) : Hd.Brow p (Function.update σ v τ) v = Hd.Brow p σ v := by sorry

alias «Auto».«HeatData».«Brow_update_σ» := P2M_Auto_HeatData_Brow_update___289bec5b5b62
