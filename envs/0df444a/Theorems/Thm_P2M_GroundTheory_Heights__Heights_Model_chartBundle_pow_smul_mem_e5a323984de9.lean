-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartBundle_pow_smul_mem_e5a323984de9
-- name    : P2M_GroundTheory_Heights__Heights_Model_chartBundle_pow_smul_mem_e5a323984de9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:48.758011+00:00
-- url     : https://prove2.me/theorems/b7633968-e693-518f-b697-3fb3a9383f00
-- title:
--   P2 M Ground Theory Heights  Heights Model chart Bundle pow smul mem e5a323984de9: P2 M Ground Theory Heights  Heights Model chart Bundle pow smul mem e5a323984de9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model chart Bundle pow smul mem e5a323984de9 construction uses the P2 M Ground Theory Heights  Heights Model chart Bundle pow smul mem e5a323984de9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L85-L87

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

theorem P2M_GroundTheory_Heights__Heights_Model_chartBundle_pow_smul_mem_e5a323984de9 (B : ChartBundle R x r E) {i : τ} {a : Ω}
    (ha : a ∈ chartRing R x i) (m : ℕ) {e : E} (he : e ∈ B.lat i) : a ^ m • e ∈ B.lat i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«chartBundle_pow_smul_mem» := P2M_GroundTheory_Heights__Heights_Model_chartBundle_pow_smul_mem_e5a323984de9
