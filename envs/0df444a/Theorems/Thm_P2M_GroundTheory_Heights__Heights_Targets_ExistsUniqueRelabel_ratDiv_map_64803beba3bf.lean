-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ratDiv_map_64803beba3bf
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ratDiv_map_64803beba3bf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:25:38.066043+00:00
-- url     : https://prove2.me/theorems/f9ac8619-1f54-469d-8017-299618bd06d2
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel rat Div map 64803beba3bf: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel rat Div map 64803beba3bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel rat Div map 64803beba3bf construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel rat Div map 64803beba3bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L237-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L237-L244

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ratDiv_map_64803beba3bf (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (ren σ f) (ren σ g) =
      Finsupp.equivMapDomain (idealEquiv σ) (ratDiv V f g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«ratDiv_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ratDiv_map_64803beba3bf
