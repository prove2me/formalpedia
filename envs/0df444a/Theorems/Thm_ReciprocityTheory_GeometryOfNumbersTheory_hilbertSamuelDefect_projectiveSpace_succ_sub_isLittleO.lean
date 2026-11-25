-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:58.512388+00:00
-- url     : https://prove2.me/theorems/431b3639-9303-472f-aa29-5e7e868e4c85
-- title:
--   Geometry Of Numbers Theory: hilbert Samuel Defect projective Space succ sub is Little O
-- statement:
--   The Geometry Of Numbers Theory construction uses the hilbert Samuel Defect projective Space succ sub is Little O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L104-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L104-L122

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO (D : ℕ) (hh : ℝ) :
    (fun n => hsDefect D (chiP D) hh (n + 1) - hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by sorry
