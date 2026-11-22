-- Prove2me | Theorems.Thm_P2M_Auto_contDiff_carlesonF__cb1ce9767a4b
-- name    : P2M_Auto_contDiff_carlesonF__cb1ce9767a4b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:00:32.258795+00:00
-- url     : https://prove2.me/theorems/a4e62b9f-0385-4352-96ed-8d5dce425109
-- title:
--   P2 M Auto cont Diff carleson F  cb1ce9767a4b: P2 M Auto cont Diff carleson F  cb1ce9767a4b
-- statement:
--   The P2 M Auto cont Diff carleson F  cb1ce9767a4b construction uses the P2 M Auto cont Diff carleson F  cb1ce9767a4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L173-L177
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L173-L177

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section

theorem P2M_Auto_contDiff_carlesonF__cb1ce9767a4b {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (carlesonF₁ g) := by sorry

alias «Auto».«contDiff_carlesonF₁» := P2M_Auto_contDiff_carlesonF__cb1ce9767a4b
