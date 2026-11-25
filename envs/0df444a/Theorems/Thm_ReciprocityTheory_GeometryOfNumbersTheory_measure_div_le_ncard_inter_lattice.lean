-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_measure_div_le_ncard_inter_lattice
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.measure_div_le_ncard_inter_lattice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:31.157819+00:00
-- url     : https://prove2.me/theorems/5392381f-60cf-5574-addd-43124481bff8
-- title:
--   Geometry Of Numbers Theory: measure div le ncard inter lattice
-- statement:
--   The Geometry Of Numbers Theory construction uses the measure div le ncard inter lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/CountZSt.lean#L63-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/CountZSt.lean#L63-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_CountZSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Module
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem ReciprocityTheory.GeometryOfNumbersTheory.measure_div_le_ncard_inter_lattice (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (hm : MeasurableSet S) :
    (μ S).toReal / (2 ^ finrank ℝ E * ZLattice.covolume L μ) ≤ ((S ∩ (L : Set E)).ncard : ℝ) := by sorry
