-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_nonneg_953ee450d2f8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_nonneg_953ee450d2f8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:20.210875+00:00
-- url     : https://prove2.me/theorems/75d52cb1-b717-4b2b-bae8-0b521cdba88d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle nonneg 953ee450d2f8: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle nonneg 953ee450d2f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle nonneg 953ee450d2f8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle nonneg 953ee450d2f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleEqZeroOfFormNotMem.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleEqZeroOfFormNotMem.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleEqZeroOfFormNotMem
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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_nonneg_953ee450d2f8 (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_nonneg» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_nonneg_953ee450d2f8
