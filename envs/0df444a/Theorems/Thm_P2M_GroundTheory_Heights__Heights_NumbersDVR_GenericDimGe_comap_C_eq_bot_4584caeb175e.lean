-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_comap_C_eq_bot_4584caeb175e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_comap_C_eq_bot_4584caeb175e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:06:08.013774+00:00
-- url     : https://prove2.me/theorems/1be93a7d-f253-479a-9a10-799d50a15d5e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge comap C eq bot 4584caeb175e: P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge comap C eq bot 4584caeb175e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge comap C eq bot 4584caeb175e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge comap C eq bot 4584caeb175e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L113-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_comap_C_eq_bot_4584caeb175e {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {σ : Type*} {ϖ : O} (hϖ : Irreducible ϖ) (Q : Ideal (MvPolynomial σ O)) [Q.IsPrime]
    (h : (C ϖ : MvPolynomial σ O) ∉ Q) : Q.comap (C : O →+* MvPolynomial σ O) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericDimGe».«comap_C_eq_bot» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_comap_C_eq_bot_4584caeb175e
