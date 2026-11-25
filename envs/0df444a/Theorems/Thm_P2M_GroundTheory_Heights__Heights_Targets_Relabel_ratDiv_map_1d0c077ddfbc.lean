-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ratDiv_map_1d0c077ddfbc
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Relabel_ratDiv_map_1d0c077ddfbc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:39.739495+00:00
-- url     : https://prove2.me/theorems/f28fc4e5-802f-49b6-a4d6-5608fcc2becf
-- title:
--   P2 M Ground Theory Heights  Heights Targets Relabel rat Div map 1d0c077ddfbc: P2 M Ground Theory Heights  Heights Targets Relabel rat Div map 1d0c077ddfbc
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Relabel rat Div map 1d0c077ddfbc construction uses the P2 M Ground Theory Heights  Heights Targets Relabel rat Div map 1d0c077ddfbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L189-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/RelabelTransport.lean#L189-L195

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

theorem P2M_GroundTheory_Heights__Heights_Targets_Relabel_ratDiv_map_1d0c077ddfbc (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv (V.map (ringEquiv F e h)) (ringEquiv F e h f) (ringEquiv F e h g) =
      Finsupp.mapDomain (Ideal.map (ringEquiv F e h)) (ratDiv V f g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Relabel».«ratDiv_map» := P2M_GroundTheory_Heights__Heights_Targets_Relabel_ratDiv_map_1d0c077ddfbc
