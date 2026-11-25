-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hsDefect_two_mul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.hsDefect_two_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:56.762067+00:00
-- url     : https://prove2.me/theorems/e9a0b7fd-c035-463d-8934-fb5f81b13912
-- title:
--   Geometry Of Numbers Theory: hs Defect two mul
-- statement:
--   The Geometry Of Numbers Theory construction uses the hs Defect two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/ClosingHS.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/ClosingHS.lean#L8-L13

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt
import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_ClosingHS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics

theorem ReciprocityTheory.GeometryOfNumbersTheory.hsDefect_two_mul (D : ℕ) (hh : ℝ) (n : ℕ) :
    hsDefect D (fun m => chiP D (2 * m)) (2 ^ (D + 1) * hh) n = hsDefect D (chiP D) hh (2 * n) := by sorry
