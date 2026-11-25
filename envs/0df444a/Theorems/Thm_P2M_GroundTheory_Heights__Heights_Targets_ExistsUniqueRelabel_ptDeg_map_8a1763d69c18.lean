-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ptDeg_map_8a1763d69c18
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ptDeg_map_8a1763d69c18
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:29.836267+00:00
-- url     : https://prove2.me/theorems/2f1673f9-caec-412c-909d-06b130e61554
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel pt Deg map 8a1763d69c18: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel pt Deg map 8a1763d69c18
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel pt Deg map 8a1763d69c18 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel pt Deg map 8a1763d69c18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L296-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L296-L300

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ptDeg_map_8a1763d69c18 (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k) :
    ptDeg (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (chartMap e σ hσ i) = ptDeg V i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«ptDeg_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ptDeg_map_8a1763d69c18
