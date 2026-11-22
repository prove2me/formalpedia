-- Prove2me | Theorems.Thm_P2M_Auto_gweight_nonneg__bb3decd414c3
-- name    : P2M_Auto_gweight_nonneg__bb3decd414c3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:16.256223+00:00
-- url     : https://prove2.me/theorems/c901663d-07fb-45a9-8eb0-f3e2e2470895
-- title:
--   P2 M Auto gweight nonneg  bb3decd414c3: P2 M Auto gweight nonneg  bb3decd414c3
-- statement:
--   The P2 M Auto gweight nonneg  bb3decd414c3 construction uses the P2 M Auto gweight nonneg  bb3decd414c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3666-L3669
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3666-L3669

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_Auto_gweight_nonneg__bb3decd414c3 (u : ι → ℝ) {h : ℝ} (hh : 0 ≤ h) (σ p : ℝ) (i : ι) :
    0 ≤ gweight u h σ p i := by sorry

alias «Auto».«gweight_nonneg'» := P2M_Auto_gweight_nonneg__bb3decd414c3
