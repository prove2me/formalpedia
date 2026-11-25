-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hilbertSamuelDefect_projectiveSpace_abs_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.hilbertSamuelDefect_projectiveSpace_abs_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:42.601113+00:00
-- url     : https://prove2.me/theorems/36166cf0-e6e2-5216-9abb-8fa29bf0576d
-- title:
--   Geometry Of Numbers Theory: hilbert Samuel Defect projective Space abs le
-- statement:
--   The Geometry Of Numbers Theory construction uses the hilbert Samuel Defect projective Space abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L84-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L84-L102

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.hilbertSamuelDefect_projectiveSpace_abs_le (D : ℕ) (hh : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, |hsDefect D (chiP D) hh n| ≤ C * (n : ℝ) ^ (D + 1) := by sorry
