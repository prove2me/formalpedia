-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isModelOver_iff_82cd95b74825
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isModelOver_iff_82cd95b74825
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:02.630889+00:00
-- url     : https://prove2.me/theorems/83ab079d-7c11-4bee-b46d-981edde0b01e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects is Model Over iff 82cd95b74825: P2 M Ground Theory Heights  Heights Numbers DVR Objects is Model Over iff 82cd95b74825
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects is Model Over iff 82cd95b74825 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects is Model Over iff 82cd95b74825 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L107-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
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
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isModelOver_iff_82cd95b74825 (P : Ideal (MRing ι O)) (d : ℕ) :
    IsModelOver P d ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.IsModelOver P d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«isModelOver_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isModelOver_iff_82cd95b74825
