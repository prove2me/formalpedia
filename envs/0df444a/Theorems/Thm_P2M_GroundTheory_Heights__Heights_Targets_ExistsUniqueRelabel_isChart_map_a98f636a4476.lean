-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isChart_map_a98f636a4476
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isChart_map_a98f636a4476
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:35.449489+00:00
-- url     : https://prove2.me/theorems/d57b1ea7-861f-414a-9b01-d4ddc2c7b72d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Chart map a98f636a4476: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Chart map a98f636a4476
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Chart map a98f636a4476 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Chart map a98f636a4476 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L277-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L277-L281

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
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isChart_map_a98f636a4476 {V : Ideal (MRingOver F ι)} {i : ∀ k, ι k} (h : IsChart V i) :
    IsChart (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (chartMap e σ hσ i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«isChart_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isChart_map_a98f636a4476
