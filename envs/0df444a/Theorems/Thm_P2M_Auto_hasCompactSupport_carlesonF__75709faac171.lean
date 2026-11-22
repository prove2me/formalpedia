-- Prove2me | Theorems.Thm_P2M_Auto_hasCompactSupport_carlesonF__75709faac171
-- name    : P2M_Auto_hasCompactSupport_carlesonF__75709faac171
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:00:40.385973+00:00
-- url     : https://prove2.me/theorems/affb6112-8e5b-404a-b88e-42c14d34fdcb
-- title:
--   P2 M Auto has Compact Support carleson F  75709faac171: P2 M Auto has Compact Support carleson F  75709faac171
-- statement:
--   The P2 M Auto has Compact Support carleson F  75709faac171 construction uses the P2 M Auto has Compact Support carleson F  75709faac171 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L186-L202
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L186-L202

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

theorem P2M_Auto_hasCompactSupport_carlesonF__75709faac171 {a : ℝ → ℝ} {A : ℝ} (ha : ∀ x, A < |x| → a x = 0)
    (ν : ℝ → ℝ) (σ : ℝ) : HasCompactSupport (carlesonF₀ a ν σ) := by sorry

alias «Auto».«hasCompactSupport_carlesonF₀» := P2M_Auto_hasCompactSupport_carlesonF__75709faac171
