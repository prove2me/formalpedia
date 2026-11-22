-- Prove2me | Theorems.Thm_P2M_Auto_HeatData_S_update_prev___eeb366000557
-- name    : P2M_Auto_HeatData_S_update_prev___eeb366000557
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:45:57.940808+00:00
-- url     : https://prove2.me/theorems/744c1cdb-8802-4b31-b594-cba8b97e4282
-- title:
--   P2 M Auto Heat Data S update prev   eeb366000557: P2 M Auto Heat Data S update prev   eeb366000557
-- statement:
--   The P2 M Auto Heat Data S update prev   eeb366000557 construction uses the P2 M Auto Heat Data S update prev   eeb366000557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3277-L3284
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3277-L3284

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

theorem P2M_Auto_HeatData_S_update_prev___eeb366000557 (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) {τ : ℝ} (hτ : 0 < τ) :
    Hd.S p (Function.update σ (v - 1) τ) v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram
      (Hd.Bprev p σ v) (gweight Hd.u Hd.h τ (p (v - 1))) := by sorry

alias «Auto».«HeatData».«S_update_prev_σ» := P2M_Auto_HeatData_S_update_prev___eeb366000557
