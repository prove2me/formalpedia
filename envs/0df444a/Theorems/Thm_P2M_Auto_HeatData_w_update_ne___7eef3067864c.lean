-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_w_update_ne___7eef3067864c
-- name    : P2M_Auto_HeatData_w_update_ne___7eef3067864c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:52.290976+00:00
-- url     : https://prove2.me/theorems/2323212b-50da-4f81-bf88-de70f30558ed
-- title:
--   P2 M Auto Heat Data w update ne   7eef3067864c: P2 M Auto Heat Data w update ne   7eef3067864c
-- statement:
--   The P2 M Auto Heat Data w update ne   7eef3067864c construction uses the P2 M Auto Heat Data w update ne   7eef3067864c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3198-L3200
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3198-L3200

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

theorem P2M_Auto_HeatData_w_update_ne___7eef3067864c {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.w p (Function.update σ v τ) k = Hd.w p σ k := by sorry

alias «Auto».«HeatData».«w_update_ne_σ» := P2M_Auto_HeatData_w_update_ne___7eef3067864c
