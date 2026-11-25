-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_comap_injective_246c205319c0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_comap_injective_246c205319c0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:33.843829+00:00
-- url     : https://prove2.me/theorems/adcb97ab-7db7-5c72-b17d-44d442f88a4e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed comap injective 246c205319c0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed coma
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed comap injective 246c205319c0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed comap injective 246c205319c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L299-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L299-L302

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] {e : K' ≃ K} {A : ∀ k', ι' k' → ι (e k') → F}
variable (hA : ∀ k', Function.Injective (Matrix.of (A k')).mulVec)
include hA

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_comap_injective_246c205319c0 :
    Function.Injective (Ideal.comap (blockLinSubst e A).toRingHom :
      Ideal (MRingOver F ι) → Ideal (MRingOver F ι')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«LinEmbed».«comap_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_comap_injective_246c205319c0
