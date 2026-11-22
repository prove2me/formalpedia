-- Prove2me | Theorems.Thm_P2M_Auto_hasDerivAt_gweight___b6d5e5597986
-- name    : P2M_Auto_hasDerivAt_gweight___b6d5e5597986
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:32:16.571715+00:00
-- url     : https://prove2.me/theorems/6040b7d7-bddb-4e7e-9134-bc26f4227c50
-- title:
--   P2 M Auto has Deriv At gweight   b6d5e5597986: P2 M Auto has Deriv At gweight   b6d5e5597986
-- statement:
--   The P2 M Auto has Deriv At gweight   b6d5e5597986 construction uses the P2 M Auto has Deriv At gweight   b6d5e5597986 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3007-L3010
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3007-L3010

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι]

theorem P2M_Auto_hasDerivAt_gweight___b6d5e5597986 (u : ι → ℝ) (h p : ℝ) {σ : ℝ} (hσ : 0 < σ) (i : ι) :
    HasDerivAt (fun τ => gweight u h τ p i) (h * gaussianD 2 σ (u i - p) / 2) σ := by sorry

alias «Auto».«hasDerivAt_gweight_σ» := P2M_Auto_hasDerivAt_gweight___b6d5e5597986
