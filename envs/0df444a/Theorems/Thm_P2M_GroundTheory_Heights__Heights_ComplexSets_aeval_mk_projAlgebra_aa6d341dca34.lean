-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_projAlgebra_aa6d341dca34
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_projAlgebra_aa6d341dca34
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:55.951138+00:00
-- url     : https://prove2.me/theorems/8c75f301-39b6-4499-bc9d-6afdaefe6f3b
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets aeval mk proj Algebra aa6d341dca34: P2 M Ground Theory Heights  Heights Complex Sets aeval mk proj Algebra aa6d341dca34
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets aeval mk proj Algebra aa6d341dca34 construction uses the P2 M Ground Theory Heights  Heights Complex Sets aeval mk proj Algebra aa6d341dca34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitive.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitive.lean#L30-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
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
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_projAlgebra_aa6d341dca34 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (G : Polynomial (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    letI := projAlgebra J A
    Polynomial.aeval (Ideal.Quotient.mk J p) G =
      Ideal.Quotient.mk J (Polynomial.eval₂ (pullback A).toRingHom p G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«aeval_mk_projAlgebra» := P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_projAlgebra_aa6d341dca34
