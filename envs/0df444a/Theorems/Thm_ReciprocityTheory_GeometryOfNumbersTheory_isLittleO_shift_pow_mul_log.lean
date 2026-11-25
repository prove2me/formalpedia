-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_isLittleO_shift_pow_mul_log
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_shift_pow_mul_log
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:12.096482+00:00
-- url     : https://prove2.me/theorems/d44de5e5-14fc-55f5-a5d6-23e34a4c84df
-- title:
--   Geometry Of Numbers Theory: is Little O shift pow mul log
-- statement:
--   The Geometry Of Numbers Theory construction uses the is Little O shift pow mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L39-L45

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_shift_pow_mul_log (D j : ℕ) :
    (fun n : ℕ => ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by sorry
