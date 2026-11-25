-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentityRightSide_congr_of_sub_mem_07359d1569a2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentityRightSide_congr_of_sub_mem_07359d1569a2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:20.168235+00:00
-- url     : https://prove2.me/theorems/5668e2d7-3a52-4616-9e86-864370120900
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cut Identity Right Side congr of sub mem 07359d1569a2: P2 M Ground Theory Heights  Heights Numbers DVR cut Identity Right Side congr of sub mem 07359d15
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cut Identity Right Side congr of sub mem 07359d1569a2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cut Identity Right Side congr of sub mem 07359d1569a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L279-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L279-L284

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentityRightSide_congr_of_sub_mem_07359d1569a2 {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ)
    (f g : MRing ι O) {s s' : MRing ι O} (h : s - s' ∈ P) {d : ℕ} (L : Fin d → K → ℤ) :
    cutIdentityRightSide ϖ P b f g s L = cutIdentityRightSide ϖ P b f g s' L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cutIdentityRightSide_congr_of_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentityRightSide_congr_of_sub_mem_07359d1569a2
