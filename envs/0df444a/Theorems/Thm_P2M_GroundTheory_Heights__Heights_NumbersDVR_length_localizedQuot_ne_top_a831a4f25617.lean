-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:31.264359+00:00
-- url     : https://prove2.me/theorems/aa85c7a4-7b9f-4864-ae0b-a077c2bef54f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot ne top a831a4f25617: P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot ne top a831a4f25617
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot ne top a831a4f25617 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot ne top a831a4f25617 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L91-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L91-L116

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617 [IsNoetherianRing A] (J W : Ideal A) [W.IsPrime]
    (hW : W ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localizedQuot_ne_top» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
