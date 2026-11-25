-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_mem_divSupp_map_iff_ded792b38804
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_mem_divSupp_map_iff_ded792b38804
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:17.898787+00:00
-- url     : https://prove2.me/theorems/8b770afd-4ec0-4043-a005-7a93489abf81
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel mem div Supp map iff ded792b38804: P2 M Ground Theory Heights  Heights Targets Relabel mem div Supp map iff ded792b38804
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel mem div Supp map iff ded792b38804 construction uses the P2 M Ground Theory Heights  Heights Targets Relabel mem div Supp map iff ded792b38804 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L163-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_mem_divSupp_map_iff_ded792b38804 (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    W.map (ringEquiv F e h) ∈ divSupp (V.map (ringEquiv F e h)) (ringEquiv F e h f) ↔
      W ∈ divSupp V f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«mem_divSupp_map_iff» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_mem_divSupp_map_iff_ded792b38804
