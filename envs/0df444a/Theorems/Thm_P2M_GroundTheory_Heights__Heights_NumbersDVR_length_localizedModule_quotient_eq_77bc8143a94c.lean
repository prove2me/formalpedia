-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_quotient_eq_77bc8143a94c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_quotient_eq_77bc8143a94c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:08.680251+00:00
-- url     : https://prove2.me/theorems/f6ade1b3-0678-4512-b508-7d352101b596
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized Module quotient eq 77bc8143a94c: P2 M Ground Theory Heights  Heights Numbers DVR length localized Module quotient eq 77bc8143a94c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized Module quotient eq 77bc8143a94c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized Module quotient eq 77bc8143a94c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPolynomialLocalizedLength.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPolynomialLocalizedLength.lean#L11-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_quotient_eq_77bc8143a94c {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localizedModule_quotient_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_quotient_eq_77bc8143a94c
