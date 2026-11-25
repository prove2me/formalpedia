-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_multAt_map_fcc1675320fb
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_multAt_map_fcc1675320fb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:53.303021+00:00
-- url     : https://prove2.me/theorems/c93ed0ca-ebe1-4542-baa8-7f38c0b909f3
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mult At map fcc1675320fb: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mult At map fcc1675320fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mult At map fcc1675320fb construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mult At map fcc1675320fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L87-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_multAt_map_fcc1675320fb (φ : MRingOver F ι ≃+* MRingOver F ι') (V W : Ideal (MRingOver F ι))
    [hW : W.IsPrime] (hVW : V ≤ W) (f : MRingOver F ι) :
    multAt (V.map (φ : MRingOver F ι →+* MRingOver F ι') ⊔ Ideal.span {φ f})
        (W.map (φ : MRingOver F ι →+* MRingOver F ι')) =
      multAt (V ⊔ Ideal.span {f}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«multAt_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_multAt_map_fcc1675320fb
