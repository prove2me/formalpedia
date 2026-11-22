-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_Bprev_update___c335d4919a13
-- name    : P2M_Auto_HeatData_Bprev_update___c335d4919a13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:33:31.4421+00:00
-- url     : https://prove2.me/theorems/b223b13a-e676-4ce3-b7f6-bc6499615457
-- title:
--   P2 M Auto Heat Data Bprev update   c335d4919a13: P2 M Auto Heat Data Bprev update   c335d4919a13
-- statement:
--   The P2 M Auto Heat Data Bprev update   c335d4919a13 construction uses the P2 M Auto Heat Data Bprev update   c335d4919a13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3242-L3244
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3242-L3244

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

theorem P2M_Auto_HeatData_Bprev_update___c335d4919a13 {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.Bprev p (Function.update σ k τ) v = Hd.Bprev p σ v := by sorry

alias «Auto».«HeatData».«Bprev_update_σ» := P2M_Auto_HeatData_Bprev_update___c335d4919a13
