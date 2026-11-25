-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isProjVarF_map_iff_c536fdc6a750
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_isProjVarF_map_iff_c536fdc6a750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:02.700028+00:00
-- url     : https://prove2.me/theorems/e9b5b6f1-019d-4313-8d97-4706c576f187
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel is Proj Var F map iff c536fdc6a750: P2 M Ground Theory Heights  Heights Targets Relabel is Proj Var F map iff c536fdc6a750
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel is Proj Var F map iff c536fdc6a750 construction uses the P2 M Ground Theory Heights  Heights Targets Relabel is Proj Var F map iff c536fdc6a750 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L122-L126

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_isProjVarF_map_iff_c536fdc6a750 (V : Ideal (MRingOver F ι)) (d : ℕ) :
    IsProjVarF (V.map (ringEquiv F e h)) d ↔ IsProjVarF V d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«isProjVarF_map_iff» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_isProjVarF_map_iff_c536fdc6a750
