-- Prove2me | Theorems.Thm_ProbabilityTheory_finitePosteriorEntropy_bounds
-- name    : ProbabilityTheory.finitePosteriorEntropy_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:49:51.300429+00:00
-- url     : https://prove2.me/theorems/2e4e8ea9-eb82-4fcb-ad84-261fc08ef511
-- title:
--   Finite conditional oracle entropy lies between zero and log cardinality
-- statement:
--   For a nonempty finite simplex-valued measurable random vector on a probability space, the expected entropy of its conditional mean lies between zero and the logarithm of the number of coordinates. Conditioning is on a sub-sigma-algebra of the explicitly named ambient measurable space.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Data.Fintype.Card

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem ProbabilityTheory.finitePosteriorEntropy_bounds
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α] [Nonempty α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (w : Ω → α → ℝ)
    (hw : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hw1 : ∀ ω, ∑ a : α, w ω a = 1) :
    0 ≤ @finitePosteriorEntropy Ω α mΩ inferInstance P m w ∧
      @finitePosteriorEntropy Ω α mΩ inferInstance P m w ≤ Real.log (Fintype.card α : ℝ) := by sorry
