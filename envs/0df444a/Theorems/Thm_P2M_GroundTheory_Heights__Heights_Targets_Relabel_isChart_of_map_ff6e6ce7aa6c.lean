-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isChart_of_map_ff6e6ce7aa6c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_isChart_of_map_ff6e6ce7aa6c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:59.893692+00:00
-- url     : https://prove2.me/theorems/de2ec644-cf6d-4b9c-bac3-9677f217e0cb
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel is Chart of map ff6e6ce7aa6c: P2 M Ground Theory Heights  Heights Targets Relabel is Chart of map ff6e6ce7aa6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel is Chart of map ff6e6ce7aa6c construction uses the P2 M Ground Theory Heights  Heights Targets Relabel is Chart of map ff6e6ce7aa6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L128-L133

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_isChart_of_map_ff6e6ce7aa6c {V : Ideal (MRingOver F ι)} {i' : ∀ k', ι' k'}
    (hi' : IsChart (V.map (ringEquiv F e h)) i') : IsChart V fun k => (h k).symm (i' (e k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«isChart_of_map» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_isChart_of_map_ff6e6ce7aa6c
