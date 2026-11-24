-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_apply_1be400d6f15c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_apply_1be400d6f15c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:39.738155+00:00
-- url     : https://prove2.me/theorems/b26fe7b2-5bfc-4983-b242-88b9c1ea802c
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv apply 1be400d6f15c: P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv apply 1be400d6f15c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv apply 1be400d6f15c construction uses the P2 M Ground Theory Heights  Heights Targets Relabel ring Equiv apply 1be400d6f15c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L45-L46

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_apply_1be400d6f15c (f : MRingOver F ι) : ringEquiv F e h f = rename (vars e h) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«ringEquiv_apply» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_apply_1be400d6f15c
