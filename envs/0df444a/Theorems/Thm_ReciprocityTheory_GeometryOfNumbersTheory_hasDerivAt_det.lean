-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hasDerivAt_det
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:55.157923+00:00
-- url     : https://prove2.me/theorems/39762c04-dce6-4bb6-86b3-8edaa360039f
-- title:
--   Geometry Of Numbers Theory: has Deriv At det
-- statement:
--   The Geometry Of Numbers Theory construction uses the has Deriv At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L31-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L31-L55

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ) (G' : Matrix (Fin r) (Fin r) ℂ)
    (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t := by sorry
