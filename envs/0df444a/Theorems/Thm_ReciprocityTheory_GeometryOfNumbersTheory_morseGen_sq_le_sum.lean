-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morseGen_sq_le_sum
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.morseGen_sq_le_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:19.786717+00:00
-- url     : https://prove2.me/theorems/5c57286f-4c18-4e6b-b7b7-e356957835be
-- title:
--   Geometry Of Numbers Theory: morse Gen sq le sum
-- statement:
--   The Geometry Of Numbers Theory construction uses the morse Gen sq le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseGenStA.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/MorseGenStA.lean#L23-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory Complex

theorem ReciprocityTheory.GeometryOfNumbersTheory.morseGen_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by sorry
