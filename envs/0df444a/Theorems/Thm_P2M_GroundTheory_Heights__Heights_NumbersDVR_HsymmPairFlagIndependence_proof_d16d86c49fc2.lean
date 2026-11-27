-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HsymmPairFlagIndependence_proof_d16d86c49fc2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HsymmPairFlagIndependence_proof_d16d86c49fc2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:57.532057+00:00
-- url     : https://prove2.me/theorems/0923ec8b-2293-45c6-a6fe-76cb877fc80e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hsymm Pair Flag Independence proof d16d86c49fc2: P2 M Ground Theory Heights  Heights Numbers DVR Hsymm Pair Flag Independence proof d16d86c49fc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hsymm Pair Flag Independence proof d16d86c49fc2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hsymm Pair Flag Independence proof d16d86c49fc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHsymmPairFlagIndependence.lean#L12-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHsymmPairFlagIndependence.lean#L12-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureNumber
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHsymmPairFlagIndependence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagIndependence_proof_ddcde7729c45

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HsymmPairFlagIndependence_proof_d16d86c49fc2 (hExp : PairNumberExpansionIndependence.Statement)
    (hClos : GenericProjClosureModel.Statement) (hSeg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HsymmPairFlagIndependence».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HsymmPairFlagIndependence_proof_d16d86c49fc2
