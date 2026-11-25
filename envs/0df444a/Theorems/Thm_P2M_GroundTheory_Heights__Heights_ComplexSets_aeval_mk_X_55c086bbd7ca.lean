-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_X_55c086bbd7ca
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_X_55c086bbd7ca
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:35.25923+00:00
-- url     : https://prove2.me/theorems/5ba98816-097c-4109-ab85-65994e47e213
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets aeval mk X 55c086bbd7ca: P2 M Ground Theory Heights  Heights Complex Sets aeval mk X 55c086bbd7ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets aeval mk X 55c086bbd7ca construction uses the P2 M Ground Theory Heights  Heights Complex Sets aeval mk X 55c086bbd7ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLeadIdealDim.lean#L34-L41

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_X_55c086bbd7ca (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (q : MvPolynomial u ℂ) :
    aeval (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) q =
      Ideal.Quotient.mk I (rename Subtype.val q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«aeval_mk_X» := P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_X_55c086bbd7ca
