-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomog_ren_f61869dec676
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomog_ren_f61869dec676
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:04.974488+00:00
-- url     : https://prove2.me/theorems/92037105-3880-5992-a8ff-41612a4b8977
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog ren f61869dec676: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog ren f61869dec676
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog ren f61869dec676 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog ren f61869dec676 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L135-L143

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
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
include hσ

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomog_ren_f61869dec676 {f : MRingOver F ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    IsMultiHomog (ren σ f) (a ∘ e.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«isMultiHomog_ren» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomog_ren_f61869dec676
