-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_deg_span_singleton
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.deg_span_singleton
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:15.575918+00:00
-- url     : https://prove2.me/theorems/05d36a66-1a42-5005-a79d-c6744d8b3b4a
-- title:
--   Geometry Of Numbers Theory: deg span singleton
-- statement:
--   The Geometry Of Numbers Theory construction uses the deg span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/InhabSt.lean#L101-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/InhabSt.lean#L101-L135

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable (K : Type*) [Field K] [NumberField K]

theorem ReciprocityTheory.GeometryOfNumbersTheory.deg_span_singleton (a : K) (ha : a ≠ 0) :
    deg (stdHerm K 1) (Submodule.span (𝓞 K) {fun _ : Fin 1 => a}) =
      -Real.log |(Algebra.norm ℚ a : ℝ)| / finrank ℚ K := by sorry
