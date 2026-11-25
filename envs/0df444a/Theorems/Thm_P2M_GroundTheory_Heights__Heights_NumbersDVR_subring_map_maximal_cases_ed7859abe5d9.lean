-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_subring_map_maximal_cases_ed7859abe5d9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_subring_map_maximal_cases_ed7859abe5d9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:29.563062+00:00
-- url     : https://prove2.me/theorems/d9fbe0f9-7181-461c-9860-9ef8fa4c10a3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR subring map maximal cases ed7859abe5d9: P2 M Ground Theory Heights  Heights Numbers DVR subring map maximal cases ed7859abe5d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR subring map maximal cases ed7859abe5d9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR subring map maximal cases ed7859abe5d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpOrderLe.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpOrderLe.lean#L14-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpOrderLe
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_subring_map_maximal_cases_ed7859abe5d9 {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«subring_map_maximal_cases» := P2M_GroundTheory_Heights__Heights_NumbersDVR_subring_map_maximal_cases_ed7859abe5d9
