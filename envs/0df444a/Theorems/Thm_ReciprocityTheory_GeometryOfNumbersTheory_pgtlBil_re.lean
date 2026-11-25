-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlBil_re
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgtlBil_re
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:49.089959+00:00
-- url     : https://prove2.me/theorems/0d0caf72-d253-4bbd-b186-269ed6456fc8
-- title:
--   Geometry Of Numbers Theory: pgtl Bil re
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgtl Bil re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L93-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Complex
variable {D : ℕ}

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgtlBil_re (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (pgtlBil B z z).re = (B z z - B (I • z) (I • z)) / 4 := by sorry
