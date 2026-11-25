-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quotient_of_surjective_637be7b48f99
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quotient_of_surjective_637be7b48f99
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:52.081279+00:00
-- url     : https://prove2.me/theorems/17c5c066-129d-5733-b9bc-d749ed50175b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length quotient of surjective 637be7b48f99: P2 M Ground Theory Heights  Heights Numbers DVR length quotient of surjective 637be7b48f99
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length quotient of surjective 637be7b48f99 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length quotient of surjective 637be7b48f99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLoc.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLoc.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLoc
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
open MvPolynomial HomLocLaurent
noncomputable section
universe u
set_option linter.style.haveILetI false

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quotient_of_surjective_637be7b48f99 {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    (h : Function.Surjective (algebraMap S C)) (I : Ideal C) :
    Module.length S (C ⧸ I) = Module.length C (C ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_quotient_of_surjective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quotient_of_surjective_637be7b48f99
