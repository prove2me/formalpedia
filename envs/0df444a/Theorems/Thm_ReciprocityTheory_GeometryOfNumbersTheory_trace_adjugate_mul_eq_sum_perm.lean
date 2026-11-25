-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_trace_adjugate_mul_eq_sum_perm
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.trace_adjugate_mul_eq_sum_perm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:52.61465+00:00
-- url     : https://prove2.me/theorems/6b33ca73-4b4a-46f3-a0a1-5ef098ddb812
-- title:
--   Geometry Of Numbers Theory: trace adjugate mul eq sum perm
-- statement:
--   The Geometry Of Numbers Theory construction uses the trace adjugate mul eq sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean#L8-L29

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.trace_adjugate_mul_eq_sum_perm {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i := by sorry
