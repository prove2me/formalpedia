-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsCohenMacaulayLocalRing_of_ringEquiv_2b90e69496b1
-- name    : P2M_GroundTheory_Heights__Heights_IsCohenMacaulayLocalRing_of_ringEquiv_2b90e69496b1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:30.514452+00:00
-- url     : https://prove2.me/theorems/3e9c9390-f8f0-42b9-85eb-f3b7c0fa451a
-- title:
--   P2 M Ground Theory Heights  Heights Is Cohen Macaulay Local Ring of ring Equiv 2b90e69496b1: P2 M Ground Theory Heights  Heights Is Cohen Macaulay Local Ring of ring Equiv 2b90e69496b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Cohen Macaulay Local Ring of ring Equiv 2b90e69496b1 construction uses the P2 M Ground Theory Heights  Heights Is Cohen Macaulay Local Ring of ring Equiv 2b90e69496b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMParameterQuotient.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMParameterQuotient.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMParameterQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_IsCohenMacaulayLocalRing_of_ringEquiv_2b90e69496b1 {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsCohenMacaulayLocalRing».«of_ringEquiv» := P2M_GroundTheory_Heights__Heights_IsCohenMacaulayLocalRing_of_ringEquiv_2b90e69496b1
