-- Prove2me | Theorems.Thm_P2M_Auto_hasCompactSupport_carlesonF__649599a31480
-- name    : P2M_Auto_hasCompactSupport_carlesonF__649599a31480
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:00:56.020551+00:00
-- url     : https://prove2.me/theorems/f039a67e-6cf3-4278-9c6c-f3d7573e9845
-- title:
--   P2 M Auto has Compact Support carleson F  649599a31480: P2 M Auto has Compact Support carleson F  649599a31480
-- statement:
--   The P2 M Auto has Compact Support carleson F  649599a31480 construction uses the P2 M Auto has Compact Support carleson F  649599a31480 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L221-L223
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L221-L223

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

theorem P2M_Auto_hasCompactSupport_carlesonF__649599a31480 {g : ℝ → ℂ} {L : ℝ} (hg : ∀ x, L < |x| → g x = 0) :
    HasCompactSupport (carlesonF₁ g) := by sorry

alias «Auto».«hasCompactSupport_carlesonF₁» := P2M_Auto_hasCompactSupport_carlesonF__649599a31480
