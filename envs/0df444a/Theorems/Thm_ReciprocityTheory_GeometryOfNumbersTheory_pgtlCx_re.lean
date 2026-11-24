-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlCx_re
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.pgtlCx_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:34.604845+00:00
-- url     : https://prove2.me/theorems/d6b842cc-ed38-4cc0-aa2b-7edb60dc1d11
-- title:
--   Geometry Of Numbers Theory: pgtl Cx re
-- statement:
--   The Geometry Of Numbers Theory construction uses the pgtl Cx re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean#L44-L45

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.pgtlCx_re (d : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) : (pgtlCx d z).re = d z := by sorry
