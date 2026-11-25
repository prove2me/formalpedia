-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_monomial_mem_originIdeal_pow_6baf16d737ed
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_monomial_mem_originIdeal_pow_6baf16d737ed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:03.721456+00:00
-- url     : https://prove2.me/theorems/49a7c768-3284-4600-b3b8-65714723c8f7
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets monomial mem origin Ideal pow 6baf16d737ed: P2 M Ground Theory Heights  Heights Complex Sets monomial mem origin Ideal pow 6baf16d737ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets monomial mem origin Ideal pow 6baf16d737ed construction uses the P2 M Ground Theory Heights  Heights Complex Sets monomial mem origin Ideal pow 6baf16d737ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L25-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_monomial_mem_originIdeal_pow_6baf16d737ed {N : ℕ} {m : Fin n →₀ ℕ} (hm : m.degree = N) :
    monomial m (1 : ℂ) ∈ originIdeal n ^ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«monomial_mem_originIdeal_pow» := P2M_GroundTheory_Heights__Heights_ComplexSets_monomial_mem_originIdeal_pow_6baf16d737ed
