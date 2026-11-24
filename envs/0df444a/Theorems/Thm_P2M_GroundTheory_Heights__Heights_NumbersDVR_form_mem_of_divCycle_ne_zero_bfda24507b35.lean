-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_form_mem_of_divCycle_ne_zero_bfda24507b35
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_form_mem_of_divCycle_ne_zero_bfda24507b35
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:56.344074+00:00
-- url     : https://prove2.me/theorems/cda2239e-6207-4f22-a890-30d23904c0f0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR form mem of div Cycle ne zero bfda24507b35: P2 M Ground Theory Heights  Heights Numbers DVR form mem of div Cycle ne zero bfda24507b35
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR form mem of div Cycle ne zero bfda24507b35 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR form mem of div Cycle ne zero bfda24507b35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LocalizedQuotientIsSimpleModuleOfMul.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LocalizedQuotientIsSimpleModuleOfMul.lean#L67-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_form_mem_of_divCycle_ne_zero_bfda24507b35 {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P x W ≠ 0) : x ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«form_mem_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_form_mem_of_divCycle_ne_zero_bfda24507b35
