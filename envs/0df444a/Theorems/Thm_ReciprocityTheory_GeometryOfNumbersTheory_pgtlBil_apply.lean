-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlBil_apply
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgtlBil_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:56.308904+00:00
-- url     : https://prove2.me/theorems/e7a762c8-6465-4590-bf57-51a4be956f09
-- title:
--   Geometry Of Numbers Theory: pgtl Bil apply
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgtl Bil apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L90-L91

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgtlBil_apply (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z w : Fin D → ℂ) :
    pgtlBil B z w = pgtlCx (pgtlDz B z) w := by sorry
