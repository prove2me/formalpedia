-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_le_of_frequently_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.le_of_frequently_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:41.250992+00:00
-- url     : https://prove2.me/theorems/35625ff0-2311-449f-b870-4f2187a1f541
-- title:
--   Geometry Of Numbers Theory: le of frequently le
-- statement:
--   The Geometry Of Numbers Theory construction uses the le of frequently le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L178-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L178-L203

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics

theorem ReciprocityTheory.GeometryOfNumbersTheory.le_of_frequently_le (D : ℕ) (chi₁ chi₂ e : ℕ → ℝ) (t₁ t₂ s : ℝ)
    (h₁ : hsDefect D chi₁ t₁ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (h₂ : hsDefect D chi₂ t₂ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (he : e =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (hle : ∃ᶠ n : ℕ in atTop,
      chi₁ n ≤ chi₂ n + s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) + e n) :
    t₁ ≤ t₂ + s := by sorry
