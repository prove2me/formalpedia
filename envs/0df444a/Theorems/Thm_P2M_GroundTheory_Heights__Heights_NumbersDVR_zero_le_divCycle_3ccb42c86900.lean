-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_zero_le_divCycle_3ccb42c86900
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_zero_le_divCycle_3ccb42c86900
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:56.421439+00:00
-- url     : https://prove2.me/theorems/617b57e1-de77-4837-8a98-aa28eed7fd4e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR zero le div Cycle 3ccb42c86900: P2 M Ground Theory Heights  Heights Numbers DVR zero le div Cycle 3ccb42c86900
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR zero le div Cycle 3ccb42c86900 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR zero le div Cycle 3ccb42c86900 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ZeroLeDivCycle.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ZeroLeDivCycle.lean#L12-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ZeroLeDivCycle
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_zero_le_divCycle_3ccb42c86900 {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) (W : Ideal (MRing ι R)) : 0 ≤ divCycle P f W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«zero_le_divCycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_zero_le_divCycle_3ccb42c86900
