-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_isPrime_f9d5f4560679
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_isPrime_f9d5f4560679
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:46.765854+00:00
-- url     : https://prove2.me/theorems/4945b1e8-164e-4457-9c17-39625f65348f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of is Prime f9d5f4560679: P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of is Prime f9d5f4560679
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of is Prime f9d5f4560679 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of is Prime f9d5f4560679 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalStrict.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalStrict.lean#L38-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalStrict
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
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_isPrime_f9d5f4560679 {W : Ideal (MRing ι R)} (hW : W.IsPrime) (u : J → MRing ι R) :
    (blowUpOf W u).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUpOf_isPrime» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_isPrime_f9d5f4560679
