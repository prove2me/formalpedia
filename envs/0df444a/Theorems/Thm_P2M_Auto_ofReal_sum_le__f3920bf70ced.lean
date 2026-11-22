-- Prove2me | Theorems.Thm_P2M_Auto_ofReal_sum_le__f3920bf70ced
-- name    : P2M_Auto_ofReal_sum_le__f3920bf70ced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:59.20762+00:00
-- url     : https://prove2.me/theorems/27b5c24e-d337-4083-9fe6-6f01868af46e
-- title:
--   P2 M Auto of Real sum le  f3920bf70ced: P2 M Auto of Real sum le  f3920bf70ced
-- statement:
--   The P2 M Auto of Real sum le  f3920bf70ced construction uses the P2 M Auto of Real sum le  f3920bf70ced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L827-L834
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L827-L834

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem P2M_Auto_ofReal_sum_le__f3920bf70ced {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by sorry

alias «Auto».«ofReal_sum_le'» := P2M_Auto_ofReal_sum_le__f3920bf70ced
