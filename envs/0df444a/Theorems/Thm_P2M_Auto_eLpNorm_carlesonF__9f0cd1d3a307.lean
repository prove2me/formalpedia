-- Prove2me | Theorems.Thm_P2M_Auto_eLpNorm_carlesonF__9f0cd1d3a307
-- name    : P2M_Auto_eLpNorm_carlesonF__9f0cd1d3a307
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:27.743628+00:00
-- url     : https://prove2.me/theorems/0db1e7bc-a99e-41f0-a4be-7bdc90be204c
-- title:
--   P2 M Auto e Lp Norm carleson F  9f0cd1d3a307: P2 M Auto e Lp Norm carleson F  9f0cd1d3a307
-- statement:
--   The P2 M Auto e Lp Norm carleson F  9f0cd1d3a307 construction uses the P2 M Auto e Lp Norm carleson F  9f0cd1d3a307 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L348-L352
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L348-L352

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

theorem P2M_Auto_eLpNorm_carlesonF__9f0cd1d3a307 {a ν : ℝ → ℝ} (ha : Measurable a) (hν : Measurable ν) (σ : ℝ) :
    eLpNorm (carlesonF₂ a ν σ) 3 volume = eLpNorm (carlesonF₂ a ν 1) 3 volume := by sorry

alias «Auto».«eLpNorm_carlesonF₂» := P2M_Auto_eLpNorm_carlesonF__9f0cd1d3a307
