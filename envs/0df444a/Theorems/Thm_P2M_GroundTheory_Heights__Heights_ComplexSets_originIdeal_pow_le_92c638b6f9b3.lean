-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_92c638b6f9b3
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_92c638b6f9b3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:18.950911+00:00
-- url     : https://prove2.me/theorems/9b973bbb-c427-4b2b-8843-fc07ce0cc856
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le 92c638b6f9b3: P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le 92c638b6f9b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le 92c638b6f9b3 construction uses the P2 M Ground Theory Heights  Heights Complex Sets origin Ideal pow le 92c638b6f9b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsOpen.lean#L46-L50

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_92c638b6f9b3 {N : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (h : ∀ m : Fin n →₀ ℕ, m.degree = N → monomial m (1 : ℂ) ∈ I) : originIdeal n ^ N ≤ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«originIdeal_pow_le» := P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_92c638b6f9b3
