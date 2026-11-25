-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomogIdeal_map_c8689bb35698
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomogIdeal_map_c8689bb35698
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:05:05.520973+00:00
-- url     : https://prove2.me/theorems/9696c816-7c76-4609-ac4e-403a9f740383
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog Ideal map c8689bb35698: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog Ideal map c868
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog Ideal map c8689bb35698 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel is Multi Homog Ideal map c8689bb35698 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L145-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomogIdeal_map_c8689bb35698 {V : Ideal (MRingOver F ι)} (h : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«isMultiHomogIdeal_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomogIdeal_map_c8689bb35698
