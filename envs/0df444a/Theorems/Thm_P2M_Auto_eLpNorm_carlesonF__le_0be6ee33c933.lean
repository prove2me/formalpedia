-- Prove2me | Theorems.Thm_P2M_Auto_eLpNorm_carlesonF__le_0be6ee33c933
-- name    : P2M_Auto_eLpNorm_carlesonF__le_0be6ee33c933
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:50.851524+00:00
-- url     : https://prove2.me/theorems/f74f28ca-0539-4f36-8156-f0d183e0a850
-- title:
--   P2 M Auto e Lp Norm carleson F  le 0be6ee33c933: P2 M Auto e Lp Norm carleson F  le 0be6ee33c933
-- statement:
--   The P2 M Auto e Lp Norm carleson F  le 0be6ee33c933 construction uses the P2 M Auto e Lp Norm carleson F  le 0be6ee33c933 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L533-L555
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L533-L555

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

theorem P2M_Auto_eLpNorm_carlesonF__le_0be6ee33c933 {g : ℝ → ℂ} {L B : ℝ} (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hg : ∀ x, L < |x| → g x = 0) :
    (eLpNorm (carlesonF₁ g) 3 volume).toReal ≤
      B * (volume (carlesonBox L)).toReal ^ (1 / 3 : ℝ) := by sorry

alias «Auto».«eLpNorm_carlesonF₁_le» := P2M_Auto_eLpNorm_carlesonF__le_0be6ee33c933
