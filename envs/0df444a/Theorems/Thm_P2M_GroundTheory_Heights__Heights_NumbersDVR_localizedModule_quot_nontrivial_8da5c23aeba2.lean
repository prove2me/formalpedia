-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedModule_quot_nontrivial_8da5c23aeba2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedModule_quot_nontrivial_8da5c23aeba2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:28.151355+00:00
-- url     : https://prove2.me/theorems/89093a5f-c4ae-4e13-b413-867791251106
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Module quot nontrivial 8da5c23aeba2: P2 M Ground Theory Heights  Heights Numbers DVR localized Module quot nontrivial 8da5c23aeba2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Module quot nontrivial 8da5c23aeba2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Module quot nontrivial 8da5c23aeba2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PLocCyclePos.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PLocCyclePos.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocCyclePos
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
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedModule_quot_nontrivial_8da5c23aeba2 {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedModule_quot_nontrivial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedModule_quot_nontrivial_8da5c23aeba2
