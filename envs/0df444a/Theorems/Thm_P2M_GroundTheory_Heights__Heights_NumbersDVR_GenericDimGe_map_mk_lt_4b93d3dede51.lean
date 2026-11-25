-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_map_mk_lt_4b93d3dede51
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_map_mk_lt_4b93d3dede51
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:30.906611+00:00
-- url     : https://prove2.me/theorems/64913f72-3ddf-4705-8a93-6cbaf2f2ba17
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge map mk lt 4b93d3dede51: P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge map mk lt 4b93d3dede51
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge map mk lt 4b93d3dede51 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge map mk lt 4b93d3dede51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L19-L28

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
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_map_mk_lt_4b93d3dede51 {p a b : Ideal R} (ha : p ≤ a) (hab : a < b) :
    a.map (Ideal.Quotient.mk p) < b.map (Ideal.Quotient.mk p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericDimGe».«map_mk_lt» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_map_mk_lt_4b93d3dede51
