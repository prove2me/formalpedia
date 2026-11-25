-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_linIdeal_cons_3e12777c3568
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_linIdeal_cons_3e12777c3568
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:35.310396+00:00
-- url     : https://prove2.me/theorems/c74b4306-3974-4206-9c7c-a853939ce147
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets lin Ideal cons 3e12777c3568: P2 M Ground Theory Heights  Heights Complex Sets lin Ideal cons 3e12777c3568
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets lin Ideal cons 3e12777c3568 construction uses the P2 M Ground Theory Heights  Heights Complex Sets lin Ideal cons 3e12777c3568 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsExists.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsExists.lean#L31-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_linIdeal_cons_3e12777c3568 {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«linIdeal_cons» := P2M_GroundTheory_Heights__Heights_ComplexSets_linIdeal_cons_3e12777c3568
