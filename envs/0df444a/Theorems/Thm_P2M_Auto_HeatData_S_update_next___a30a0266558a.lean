-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_S_update_next___a30a0266558a
-- name    : P2M_Auto_HeatData_S_update_next___a30a0266558a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:45:35.778865+00:00
-- url     : https://prove2.me/theorems/5a6a7265-3ad9-4a7e-9d54-025e60b49771
-- title:
--   P2 M Auto Heat Data S update next   a30a0266558a: P2 M Auto Heat Data S update next   a30a0266558a
-- statement:
--   The P2 M Auto Heat Data S update next   a30a0266558a construction uses the P2 M Auto Heat Data S update next   a30a0266558a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3261-L3268
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3261-L3268

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

theorem P2M_Auto_HeatData_S_update_next___a30a0266558a (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) {τ : ℝ} (hτ : 0 < τ) :
    Hd.S p (Function.update σ (v + 1) τ) v = wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1)) + wGram
      (Hd.Bnext p σ v) (gweight Hd.u Hd.h τ (p (v + 1))) := by sorry

alias «Auto».«HeatData».«S_update_next_σ» := P2M_Auto_HeatData_S_update_next___a30a0266558a
