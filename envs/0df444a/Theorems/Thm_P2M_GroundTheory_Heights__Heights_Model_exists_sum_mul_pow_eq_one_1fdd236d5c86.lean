-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:26.236518+00:00
-- url     : https://prove2.me/theorems/acc7f705-1446-4759-a7b0-e6b777fc2587
-- title:
--   P2 M Ground Theory Heights  Heights Model exists sum mul pow eq one 1fdd236d5c86: P2 M Ground Theory Heights  Heights Model exists sum mul pow eq one 1fdd236d5c86
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists sum mul pow eq one 1fdd236d5c86 construction uses the P2 M Ground Theory Heights  Heights Model exists sum mul pow eq one 1fdd236d5c86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueSat.lean#L44-L60

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
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]

theorem P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86 (A : S) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ A)
    (hc : ∀ l, c l ∈ A) (h1 : ∑ l, c l * f l = 1) (N : ℕ) :
    ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ N = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_sum_mul_pow_eq_one» := P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86
