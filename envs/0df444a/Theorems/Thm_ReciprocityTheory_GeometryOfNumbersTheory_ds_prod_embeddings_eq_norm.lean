-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_prod_embeddings_eq_norm
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.ds_prod_embeddings_eq_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:34.963675+00:00
-- url     : https://prove2.me/theorems/3b07f6d5-189b-4e76-99e1-888448ef1c28
-- title:
--   Geometry Of Numbers Theory: ds prod embeddings eq norm
-- statement:
--   The Geometry Of Numbers Theory construction uses the ds prod embeddings eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L148-L151

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.ds_prod_embeddings_eq_norm (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by sorry
