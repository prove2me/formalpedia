-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_isLittleO_succ_pow_sub
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_succ_pow_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:26.177585+00:00
-- url     : https://prove2.me/theorems/273951ea-5336-417d-9c02-ba6b7fabcb83
-- title:
--   Geometry Of Numbers Theory: is Little O succ pow sub
-- statement:
--   The Geometry Of Numbers Theory construction uses the is Little O succ pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L47-L51

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.isLittleO_succ_pow_sub (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by sorry
