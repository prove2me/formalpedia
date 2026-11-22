-- Prove2me | Theorems.Thm_P2M_Auto_contDiff_carlesonF__9fa96f04780b
-- name    : P2M_Auto_contDiff_carlesonF__9fa96f04780b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:10.744803+00:00
-- url     : https://prove2.me/theorems/8910094e-a488-4fa8-b127-199687b5727e
-- title:
--   P2 M Auto cont Diff carleson F  9fa96f04780b: P2 M Auto cont Diff carleson F  9fa96f04780b
-- statement:
--   The P2 M Auto cont Diff carleson F  9fa96f04780b construction uses the P2 M Auto cont Diff carleson F  9fa96f04780b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L179-L184
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L179-L184

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

theorem P2M_Auto_contDiff_carlesonF__9fa96f04780b {a ν : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hν : ContDiff ℝ ∞ ν) (σ : ℝ) :
    ContDiff ℝ ∞ (carlesonF₂ a ν σ) := by sorry

alias «Auto».«contDiff_carlesonF₂» := P2M_Auto_contDiff_carlesonF__9fa96f04780b
