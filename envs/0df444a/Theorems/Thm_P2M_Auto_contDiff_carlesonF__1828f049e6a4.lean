-- Prove2me | Theorems.Thm_P2M_Auto_contDiff_carlesonF__1828f049e6a4
-- name    : P2M_Auto_contDiff_carlesonF__1828f049e6a4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:00:44.303079+00:00
-- url     : https://prove2.me/theorems/f93643bc-4ee6-4b03-b107-4dde818765bc
-- title:
--   P2 M Auto cont Diff carleson F  1828f049e6a4: P2 M Auto cont Diff carleson F  1828f049e6a4
-- statement:
--   The P2 M Auto cont Diff carleson F  1828f049e6a4 construction uses the P2 M Auto cont Diff carleson F  1828f049e6a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L166-L171
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L166-L171

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

theorem P2M_Auto_contDiff_carlesonF__1828f049e6a4 {a ν : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hν : ContDiff ℝ ∞ ν) (σ : ℝ) :
    ContDiff ℝ ∞ (carlesonF₀ a ν σ) := by sorry

alias «Auto».«contDiff_carlesonF₀» := P2M_Auto_contDiff_carlesonF__1828f049e6a4
