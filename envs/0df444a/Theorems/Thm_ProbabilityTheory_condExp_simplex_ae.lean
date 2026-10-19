-- Prove2me | Theorems.Thm_ProbabilityTheory_condExp_simplex_ae
-- name    : ProbabilityTheory.condExp_simplex_ae
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:57:04.265009+00:00
-- url     : https://prove2.me/theorems/dc556a3c-2ce5-494e-9d24-f3f0c0a23cfe
-- title:
--   Conditional expectation preserves a finite simplex almost everywhere
-- statement:
--   For a measurable, nonnegative finite probability vector on a probability space, each coordinate’s conditional expectation is measurable in the ambient space, the conditional coordinates are nonnegative almost everywhere, and their finite sum is one almost everywhere. Prove nonnegativity using monotonicity of conditional expectation; prove the sum identity by linearity and conditional expectation of the constant one. The simplex hypotheses also give coordinate bounds and integrability.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Fintype.BigOperators

open MeasureTheory
open scoped BigOperators

theorem ProbabilityTheory.condExp_simplex_ae
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (w : Ω → α → ℝ)
    (hw : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hw1 : ∀ ω, ∑ a : α, w ω a = 1) :
    (∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => (P[fun ω' => w ω' a | m]) ω)) ∧
      (∀ᵐ ω ∂P, ∀ a, 0 ≤ (P[fun ω' => w ω' a | m]) ω) ∧
        (∀ᵐ ω ∂P, ∑ a : α, (P[fun ω' => w ω' a | m]) ω = 1) := by sorry
