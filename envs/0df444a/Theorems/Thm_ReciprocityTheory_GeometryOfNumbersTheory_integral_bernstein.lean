-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_bernstein
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:23.71251+00:00
-- url     : https://prove2.me/theorems/6edcba66-8e22-42b7-8759-f05a7e06835d
-- title:
--   Geometry Of Numbers Theory: integral bernstein
-- statement:
--   The Geometry Of Numbers Theory construction uses the integral bernstein property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L140-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L140-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory
open scoped ComplexOrder

theorem ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein (D i : ℕ) (hi : i ≤ D) :
    ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) = 1 / (D + 1 : ℝ) := by sorry
