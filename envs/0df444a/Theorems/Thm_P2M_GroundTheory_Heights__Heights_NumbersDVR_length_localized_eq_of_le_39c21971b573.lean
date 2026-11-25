-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_le_39c21971b573
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_le_39c21971b573
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:07.466258+00:00
-- url     : https://prove2.me/theorems/12993da2-f0da-46d5-a393-89d55615e557
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of le 39c21971b573: P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of le 39c21971b573
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of le 39c21971b573 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of le 39c21971b573 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L23-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
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
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_le_39c21971b573 {J J'' W : Ideal A} [W.IsPrime] (hle : J ≤ J'')
    (h : ∀ x ∈ J'', ∃ t ∉ W, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J'')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localized_eq_of_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_le_39c21971b573
