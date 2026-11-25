-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_span_901177580971
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_span_901177580971
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:57.62973+00:00
-- url     : https://prove2.me/theorems/c69cab7d-5e12-4129-95bd-c6b9cb98b501
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le span 901177580971: P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le span 901177580971
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le span 901177580971 construction uses the P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le span 901177580971 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L33-L44

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_span_901177580971 (N : ℕ) :
    originIdeal n ^ N ≤
      Ideal.span {p | ∃ m : Fin n →₀ ℕ, m.degree = N ∧ monomial m (1 : ℂ) = p} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«originIdeal_pow_le_span» := P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_span_901177580971
