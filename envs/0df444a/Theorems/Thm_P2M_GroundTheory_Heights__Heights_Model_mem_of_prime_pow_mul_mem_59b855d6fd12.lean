-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_of_prime_pow_mul_mem_59b855d6fd12
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_of_prime_pow_mul_mem_59b855d6fd12
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:02.566599+00:00
-- url     : https://prove2.me/theorems/bfbd867a-5ef1-473d-85b1-6a853a3a2794
-- title:
--   P2 M Ground Theory Heights  Heights Model mem of prime pow mul mem 59b855d6fd12: P2 M Ground Theory Heights  Heights Model mem of prime pow mul mem 59b855d6fd12
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem of prime pow mul mem 59b855d6fd12 construction uses the P2 M Ground Theory Heights  Heights Model mem of prime pow mul mem 59b855d6fd12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L47-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
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
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Model_mem_of_prime_pow_mul_mem_59b855d6fd12 {A : Subalgebra ℤ Ω} {p : ℕ} (hp : p.Prime) {s : ℤ}
    (hs : ¬ (p : ℤ) ∣ s) (N : ℕ) {y : Ω} (h1 : (((p : ℤ) : Ω)) ^ N * y ∈ A)
    (h2 : (s : Ω) * y ∈ A) : y ∈ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_of_prime_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_Model_mem_of_prime_pow_mul_mem_59b855d6fd12
