-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:06.898021+00:00
-- url     : https://prove2.me/theorems/82103773-c2bd-4b5c-ba8c-ba51eeb48343
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle congr of sub mem 56ff166eaee6: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle congr of sub mem 56ff166eaee6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle congr of sub mem 56ff166eaee6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle congr of sub mem 56ff166eaee6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L258-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L258-L277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6 {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {s s' : MRing ι R} (h : s - s' ∈ P) : divCycle P s = divCycle P s' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_congr_of_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6
