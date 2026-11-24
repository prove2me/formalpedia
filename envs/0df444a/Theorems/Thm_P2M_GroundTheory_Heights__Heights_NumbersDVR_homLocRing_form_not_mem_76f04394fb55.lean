-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:05.802797+00:00
-- url     : https://prove2.me/theorems/877c4838-2946-4ab8-82ab-f7de72737499
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR hom Loc Ring form not mem 76f04394fb55: P2 M Ground Theory Heights  Heights Numbers DVR hom Loc Ring form not mem 76f04394fb55
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR hom Loc Ring form not mem 76f04394fb55 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR hom Loc Ring form not mem 76f04394fb55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingLocal.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingLocal.lean#L13-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {R : Type u} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W)
    (c : K → ℕ) : ∃ g : MRing ι R, IsMultiHomog g c ∧ g ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«homLocRing_form_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55
