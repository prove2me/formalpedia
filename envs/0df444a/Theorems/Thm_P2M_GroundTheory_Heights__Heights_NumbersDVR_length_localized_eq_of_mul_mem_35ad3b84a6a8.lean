-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:54.001188+00:00
-- url     : https://prove2.me/theorems/7fece81f-ba3c-491d-902f-d1f31fc03cba
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of mul mem 35ad3b84a6a8: P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of mul mem 35ad3b84a6a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of mul mem 35ad3b84a6a8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized eq of mul mem 35ad3b84a6a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L52-L62

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8 {J J' W : Ideal A} [W.IsPrime] {s t : A} (hs : s ∉ W)
    (ht : t ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localized_eq_of_mul_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8
