-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_sum_log_normSq_embeddings
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.ds_sum_log_normSq_embeddings
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:53.400148+00:00
-- url     : https://prove2.me/theorems/c5e976b6-ab4f-4fc7-9697-19d045fdc871
-- title:
--   Geometry Of Numbers Theory: ds sum log norm Sq embeddings
-- statement:
--   The Geometry Of Numbers Theory construction uses the ds sum log norm Sq embeddings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L153-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L153-L161

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {K : Type*} [Field K] [NumberField K]

theorem ReciprocityTheory.GeometryOfNumbersTheory.ds_sum_log_normSq_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by sorry
