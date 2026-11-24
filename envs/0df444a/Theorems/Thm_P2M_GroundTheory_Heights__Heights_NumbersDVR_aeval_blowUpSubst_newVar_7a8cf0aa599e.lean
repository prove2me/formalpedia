-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:14.213542+00:00
-- url     : https://prove2.me/theorems/21a9d193-9765-4a05-9d86-a26b00e4afb1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst new Var 7a8cf0aa599e: P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst new Var 7a8cf0aa599e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst new Var 7a8cf0aa599e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR aeval blow Up Subst new Var 7a8cf0aa599e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L90-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e (P : Ideal (MRing ι R)) (u : J → MRing ι R) (k : J) :
    aeval (blowUpSubst P u) (newVar k : MRing (extIdx ι J) R) = Polynomial.C (Ideal.Quotient.mk P (u k)) * Polynomial.X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«aeval_blowUpSubst_newVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e
