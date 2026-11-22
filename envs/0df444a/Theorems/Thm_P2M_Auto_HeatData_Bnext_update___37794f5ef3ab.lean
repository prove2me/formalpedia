-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_Bnext_update___37794f5ef3ab
-- name    : P2M_Auto_HeatData_Bnext_update___37794f5ef3ab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:33:15.534257+00:00
-- url     : https://prove2.me/theorems/5960dfd6-67e9-4375-af72-3abead76c3fc
-- title:
--   P2 M Auto Heat Data Bnext update   37794f5ef3ab: P2 M Auto Heat Data Bnext update   37794f5ef3ab
-- statement:
--   The P2 M Auto Heat Data Bnext update   37794f5ef3ab construction uses the P2 M Auto Heat Data Bnext update   37794f5ef3ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3234-L3236
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3234-L3236

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

theorem P2M_Auto_HeatData_Bnext_update___37794f5ef3ab {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.Bnext p (Function.update σ k τ) v = Hd.Bnext p σ v := by sorry

alias «Auto».«HeatData».«Bnext_update_σ» := P2M_Auto_HeatData_Bnext_update___37794f5ef3ab
