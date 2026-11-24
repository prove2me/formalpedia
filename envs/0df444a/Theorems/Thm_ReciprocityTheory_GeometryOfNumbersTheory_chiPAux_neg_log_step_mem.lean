-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_step_mem
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_step_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:05.333748+00:00
-- url     : https://prove2.me/theorems/7f4acaaa-c638-458c-85dd-927a50dd91c6
-- title:
--   Geometry Of Numbers Theory: chi PAux neg log step mem
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux neg log step mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L228-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L228-L251

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_step_mem (D n : ℕ) (a : Fin (D + 1) → ℕ) (ha : a ∈ Finset.Nat.antidiagonalTuple (D + 1) n) :
    0 ≤ -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ∧
      -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ≤ Real.log ((n : ℝ) + D + 1) := by sorry
