-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_isLittleO_pow_mul_log
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_pow_mul_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:28.589046+00:00
-- url     : https://prove2.me/theorems/f68f9c59-d48b-44fc-9014-cecc0692f21c
-- title:
--   Geometry Of Numbers Theory: is Little O pow mul log
-- statement:
--   The Geometry Of Numbers Theory construction uses the is Little O pow mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L12-L26

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_pow_mul_log (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by sorry
