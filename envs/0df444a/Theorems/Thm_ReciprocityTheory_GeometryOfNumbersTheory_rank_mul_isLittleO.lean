-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_rank_mul_isLittleO
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.rank_mul_isLittleO
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:41.465068+00:00
-- url     : https://prove2.me/theorems/5b930806-e123-47e1-a934-b658292a2f46
-- title:
--   Geometry Of Numbers Theory: rank mul is Little O
-- statement:
--   The Geometry Of Numbers Theory construction uses the rank mul is Little O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L205-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L205-L217

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.rank_mul_isLittleO (D : ℕ) (r : ℕ → ℝ) (δ t : ℝ)
    (hr : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / (D.factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ D) :
    (fun n : ℕ => (n : ℝ) * r n * t -
        ((D + 1 : ℝ) * δ * t) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by sorry
