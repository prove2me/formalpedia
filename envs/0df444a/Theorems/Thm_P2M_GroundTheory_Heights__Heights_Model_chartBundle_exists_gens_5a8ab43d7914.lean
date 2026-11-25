-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartBundle_exists_gens_5a8ab43d7914
-- name    : P2M_GroundTheory_Heights__Heights_Model_chartBundle_exists_gens_5a8ab43d7914
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:01.800496+00:00
-- url     : https://prove2.me/theorems/499022e4-0878-4c65-b5dc-418d5fe964aa
-- title:
--   P2 M Ground Theory Heights  Heights Model chart Bundle exists gens 5a8ab43d7914: P2 M Ground Theory Heights  Heights Model chart Bundle exists gens 5a8ab43d7914
-- statement:
--   The P2 M Ground Theory Heights  Heights Model chart Bundle exists gens 5a8ab43d7914 construction uses the P2 M Ground Theory Heights  Heights Model chart Bundle exists gens 5a8ab43d7914 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L89-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L89-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {R : Type*} [CommRing R] [Algebra R Ω] {τ : Type*} {x : τ → Ω} {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Model_chartBundle_exists_gens_5a8ab43d7914 (B : ChartBundle R x r E) {i : τ} (hi : x i ≠ 0) :
    ∃ (k : ℕ) (G : Fin k × Fin r → E), (∀ j, G j ∈ B.lat i) ∧
      ∀ e ∈ B.lat i, ∃ β : Fin k × Fin r → Ω, (∀ j, β j ∈ chartRing R x i) ∧
        e = ∑ j, β j • G j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«chartBundle_exists_gens» := P2M_GroundTheory_Heights__Heights_Model_chartBundle_exists_gens_5a8ab43d7914
