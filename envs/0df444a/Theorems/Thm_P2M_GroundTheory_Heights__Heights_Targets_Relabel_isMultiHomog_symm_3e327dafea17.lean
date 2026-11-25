-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_symm_3e327dafea17
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_symm_3e327dafea17
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:24.766017+00:00
-- url     : https://prove2.me/theorems/5ad3d984-9620-4efe-bd53-d1cb9b7f9bcf
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel is Multi Homog symm 3e327dafea17: P2 M Ground Theory Heights  Heights Targets Relabel is Multi Homog symm 3e327dafea17
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel is Multi Homog symm 3e327dafea17 construction uses the P2 M Ground Theory Heights  Heights Targets Relabel is Multi Homog symm 3e327dafea17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L94-L105

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_symm_3e327dafea17 {g : MRingOver F ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog ((ringEquiv F e h).symm g) (d ∘ e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«isMultiHomog_symm» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_symm_3e327dafea17
