-- Prove2me | Theorems.Thm_P2M_Auto_hasCompactSupport_carlesonF__af972bad9b1b
-- name    : P2M_Auto_hasCompactSupport_carlesonF__af972bad9b1b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:03.815261+00:00
-- url     : https://prove2.me/theorems/2e0780d3-f994-4fca-83b1-d87d0878be6b
-- title:
--   P2 M Auto has Compact Support carleson F  af972bad9b1b: P2 M Auto has Compact Support carleson F  af972bad9b1b
-- statement:
--   The P2 M Auto has Compact Support carleson F  af972bad9b1b construction uses the P2 M Auto has Compact Support carleson F  af972bad9b1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L225-L241
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L225-L241

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

theorem P2M_Auto_hasCompactSupport_carlesonF__af972bad9b1b {a : ℝ → ℝ} {A : ℝ} (ha : ∀ x, A < |x| → a x = 0)
    (ν : ℝ → ℝ) (σ : ℝ) : HasCompactSupport (carlesonF₂ a ν σ) := by sorry

alias «Auto».«hasCompactSupport_carlesonF₂» := P2M_Auto_hasCompactSupport_carlesonF__af972bad9b1b
