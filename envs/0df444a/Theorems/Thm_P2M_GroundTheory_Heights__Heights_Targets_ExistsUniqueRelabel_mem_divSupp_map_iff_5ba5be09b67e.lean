-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_divSupp_map_iff_5ba5be09b67e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_divSupp_map_iff_5ba5be09b67e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:35.146124+00:00
-- url     : https://prove2.me/theorems/51b20d57-a26b-52a8-a395-a7d02577bcdd
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem div Supp map iff 5ba5be09b67e: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem div Supp map iff 5ba5be09b67e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem div Supp map iff 5ba5be09b67e construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel mem div Supp map iff 5ba5be09b67e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L198-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L198-L207

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_divSupp_map_iff_5ba5be09b67e (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ∈
        divSupp (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (ren σ f) ↔
      W ∈ divSupp V f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«mem_divSupp_map_iff» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_divSupp_map_iff_5ba5be09b67e
