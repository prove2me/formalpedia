-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentity_iff_b8b36a9a2a81
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentity_iff_b8b36a9a2a81
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:39.119873+00:00
-- url     : https://prove2.me/theorems/27dc4bc1-9239-4cf8-9494-b46683ff7b47
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cut Identity iff b8b36a9a2a81: P2 M Ground Theory Heights  Heights Numbers DVR cut Identity iff b8b36a9a2a81
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cut Identity iff b8b36a9a2a81 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cut Identity iff b8b36a9a2a81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L88-L91

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentity_iff_b8b36a9a2a81 (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) :
    cutIdentity ϖ P b f g c s L ↔ cutIdentityLeftSide P f g c L = cutIdentityRightSide ϖ P b f g s L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cutIdentity_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentity_iff_b8b36a9a2a81
