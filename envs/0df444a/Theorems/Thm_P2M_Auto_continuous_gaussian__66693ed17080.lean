-- Prove2me | Theorems.Thm_P2M_Auto_continuous_gaussian__66693ed17080
-- name    : P2M_Auto_continuous_gaussian__66693ed17080
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:08.765558+00:00
-- url     : https://prove2.me/theorems/4485e52e-fc15-4557-96eb-2567060defea
-- title:
--   P2 M Auto continuous gaussian  66693ed17080: P2 M Auto continuous gaussian  66693ed17080
-- statement:
--   The P2 M Auto continuous gaussian  66693ed17080 construction uses the P2 M Auto continuous gaussian  66693ed17080 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5726-L5728
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5726-L5728

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

theorem P2M_Auto_continuous_gaussian__66693ed17080 (σ : ℝ) : Continuous (gaussian σ) := by sorry

alias «Auto».«continuous_gaussian'» := P2M_Auto_continuous_gaussian__66693ed17080
