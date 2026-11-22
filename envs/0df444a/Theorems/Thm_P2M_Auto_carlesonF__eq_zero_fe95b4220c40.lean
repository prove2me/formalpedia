-- Prove2me | Theorems.Thm_P2M_Auto_carlesonF__eq_zero_fe95b4220c40
-- name    : P2M_Auto_carlesonF__eq_zero_fe95b4220c40
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:28.525474+00:00
-- url     : https://prove2.me/theorems/4b4d7c9f-3a81-4e92-aa24-1feacfd923e7
-- title:
--   P2 M Auto carleson F  eq zero fe95b4220c40: P2 M Auto carleson F  eq zero fe95b4220c40
-- statement:
--   The P2 M Auto carleson F  eq zero fe95b4220c40 construction uses the P2 M Auto carleson F  eq zero fe95b4220c40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L209-L219
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L209-L219

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

theorem P2M_Auto_carlesonF__eq_zero_fe95b4220c40 {g : ℝ → ℂ} {L : ℝ} (hg : ∀ x, L < |x| → g x = 0) {p : ℝ × ℝ}
    (hp : p ∉ carlesonBox L) : carlesonF₁ g p = 0 := by sorry

alias «Auto».«carlesonF₁_eq_zero» := P2M_Auto_carlesonF__eq_zero_fe95b4220c40
