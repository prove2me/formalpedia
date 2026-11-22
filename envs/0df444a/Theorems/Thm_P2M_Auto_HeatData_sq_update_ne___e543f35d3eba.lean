-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_sq_update_ne___e543f35d3eba
-- name    : P2M_Auto_HeatData_sq_update_ne___e543f35d3eba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:57.882486+00:00
-- url     : https://prove2.me/theorems/2caa711a-6dde-479c-be0c-d8ab6c849d35
-- title:
--   P2 M Auto Heat Data sq update ne   e543f35d3eba: P2 M Auto Heat Data sq update ne   e543f35d3eba
-- statement:
--   The P2 M Auto Heat Data sq update ne   e543f35d3eba construction uses the P2 M Auto Heat Data sq update ne   e543f35d3eba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3218-L3220
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3218-L3220

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

theorem P2M_Auto_HeatData_sq_update_ne___e543f35d3eba {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.sqw p (Function.update σ v τ) k = Hd.sqw p σ k := by sorry

alias «Auto».«HeatData».«sq_update_ne_σ» := P2M_Auto_HeatData_sq_update_ne___e543f35d3eba
