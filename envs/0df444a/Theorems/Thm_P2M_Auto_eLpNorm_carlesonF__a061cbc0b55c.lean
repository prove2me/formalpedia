-- Prove2me | Theorems.Thm_P2M_Auto_eLpNorm_carlesonF__a061cbc0b55c
-- name    : P2M_Auto_eLpNorm_carlesonF__a061cbc0b55c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:27.081051+00:00
-- url     : https://prove2.me/theorems/c0e67cfa-57a8-4637-8aad-714ea7d1d455
-- title:
--   P2 M Auto e Lp Norm carleson F  a061cbc0b55c: P2 M Auto e Lp Norm carleson F  a061cbc0b55c
-- statement:
--   The P2 M Auto e Lp Norm carleson F  a061cbc0b55c construction uses the P2 M Auto e Lp Norm carleson F  a061cbc0b55c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L342-L346
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L342-L346

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

theorem P2M_Auto_eLpNorm_carlesonF__a061cbc0b55c {a ν : ℝ → ℝ} (ha : Measurable a) (hν : Measurable ν) (σ : ℝ) :
    eLpNorm (carlesonF₀ a ν σ) 3 volume = eLpNorm (carlesonF₀ a ν 1) 3 volume := by sorry

alias «Auto».«eLpNorm_carlesonF₀» := P2M_Auto_eLpNorm_carlesonF__a061cbc0b55c
