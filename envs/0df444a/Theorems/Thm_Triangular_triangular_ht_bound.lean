-- Prove2me | Theorems.Thm_Triangular_triangular_ht_bound
-- name    : Triangular.triangular_ht_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:10:53.342596+00:00
-- url     : https://prove2.me/theorems/4e40ebf3-ff16-4cbb-9182-83555c9d5fe4
-- title:
--   Triangular: triangular ht bound
-- statement:
--   The triangular Hilbert transform is bounded on `L³ × L³ × L³`.
--   *Implementation notes:*
--   We formulate the bound as an a priori estimate on Schwartz functions as is common practice.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Theorems.lean#L28-L31
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Theorems.lean#L28-L31

module
public import Definitions.Def_Triangular_Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Definitions.Def_Triangular_Auto_Carleson
public import Definitions.Def_Triangular_Theorems
public import Theorems.Thm_Auto_triangular_ht_bound

set_option autoImplicit true
@[expose] public section
public section
open Triangular
open MeasureTheory SchwartzMap Topology Filter Function

theorem Triangular.triangular_ht_bound :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : 𝓢(ℝ × ℝ, ℂ),
      ‖T F₀ F₁ F₂‖ₑ ≤ ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 := by sorry
