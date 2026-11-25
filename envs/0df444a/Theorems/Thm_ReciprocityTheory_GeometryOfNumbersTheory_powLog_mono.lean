-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_powLog_mono
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.powLog_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:17.926576+00:00
-- url     : https://prove2.me/theorems/ab9f8447-8fba-5dd4-ba14-b86c94d2633c
-- title:
--   Geometry Of Numbers Theory: pow Log mono
-- statement:
--   The Geometry Of Numbers Theory construction uses the pow Log mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/DefectSt.lean#L53-L60

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.powLog_mono (D : ℕ) {m n : ℕ} (h : m ≤ n) :
    (m : ℝ) ^ D * Real.log ((m : ℝ) + 1) ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by sorry
