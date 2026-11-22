-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_T_update___6afbb602a2e7
-- name    : P2M_Auto_HeatData_T_update___6afbb602a2e7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:45:00.850856+00:00
-- url     : https://prove2.me/theorems/00ff3481-c440-4488-b072-bbe0db526015
-- title:
--   P2 M Auto Heat Data T update   6afbb602a2e7: P2 M Auto Heat Data T update   6afbb602a2e7
-- statement:
--   The P2 M Auto Heat Data T update   6afbb602a2e7 construction uses the P2 M Auto Heat Data T update   6afbb602a2e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3250-L3252
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3250-L3252

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

theorem P2M_Auto_HeatData_T_update___6afbb602a2e7 (hh : 0 ≤ Hd.h) {v : Fin 3} {τ : ℝ} (hτ : 0 < τ) :
    Hd.T p (Function.update σ v τ) v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h τ (p v)) := by sorry

alias «Auto».«HeatData».«T_update_σ» := P2M_Auto_HeatData_T_update___6afbb602a2e7
