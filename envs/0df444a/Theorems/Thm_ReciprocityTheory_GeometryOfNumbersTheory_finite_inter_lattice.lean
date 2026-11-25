-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_finite_inter_lattice
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.finite_inter_lattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:02.02495+00:00
-- url     : https://prove2.me/theorems/cef529d6-733d-4428-a364-cd1c4cbacfdc
-- title:
--   Geometry Of Numbers Theory: finite inter lattice
-- statement:
--   The Geometry Of Numbers Theory construction uses the finite inter lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/CountZSt.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/CountZSt.lean#L11-L16

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.finite_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hb : Bornology.IsBounded S) : (S ∩ (L : Set E)).Finite := by sorry
