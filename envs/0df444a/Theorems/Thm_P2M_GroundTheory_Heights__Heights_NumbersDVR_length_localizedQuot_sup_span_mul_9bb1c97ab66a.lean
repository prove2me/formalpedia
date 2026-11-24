-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:34.634464+00:00
-- url     : https://prove2.me/theorems/b55d33db-91a5-42cb-8287-cce1a89bc03e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot sup span mul 9bb1c97ab66a: P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot sup span mul 9bb1c97ab66a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot sup span mul 9bb1c97ab66a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot sup span mul 9bb1c97ab66a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L21-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L21-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
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
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a (P W : Ideal A) [P.IsPrime] [W.IsPrime] {x : A} (y : A)
    (hx : x ∉ P) :
    Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x * y}))) =
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {y}))) +
        Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x}))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localizedQuot_sup_span_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a
