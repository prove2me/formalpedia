-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hasDerivAt_log_det
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_log_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:26.796312+00:00
-- url     : https://prove2.me/theorems/fed55259-9e29-49f6-add3-7b97e7251b9c
-- title:
--   Geometry Of Numbers Theory: has Deriv At log det
-- statement:
--   The Geometry Of Numbers Theory construction uses the has Deriv At log det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L57-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L57-L76

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_log_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : (G t).PosDef) :
    HasDerivAt (fun s => Real.log (G s).det.re) ((G t)⁻¹ * G').trace.re t := by sorry
