-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_divCycle_map_apply_89989eae05a8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_divCycle_map_apply_89989eae05a8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:41.835414+00:00
-- url     : https://prove2.me/theorems/8aada914-dcc8-5f44-b3a6-e2d0a2663f5b
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel div Cycle map apply 89989eae05a8: P2 M Ground Theory Heights  Heights Targets Relabel div Cycle map apply 89989eae05a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel div Cycle map apply 89989eae05a8 construction uses the P2 M Ground Theory Heights  Heights Targets Relabel div Cycle map apply 89989eae05a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L180-L187

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_divCycle_map_apply_89989eae05a8 (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    divCycle (V.map (ringEquiv F e h)) (ringEquiv F e h f) (W.map (ringEquiv F e h)) =
      divCycle V f W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«divCycle_map_apply» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_divCycle_map_apply_89989eae05a8
