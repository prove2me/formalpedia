-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomogIdeal_comap_a23a80c5c85c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomogIdeal_comap_a23a80c5c85c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:51.381128+00:00
-- url     : https://prove2.me/theorems/55ceac7d-4b96-4a9d-bcd7-bbd31f14e24d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Multi Homog Ideal comap a23a80c5c85c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Multi Homog Ideal comap a23a80c5c85c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Multi Homog Ideal comap a23a80c5c85c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L215-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L215-L229

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomogIdeal_comap_a23a80c5c85c {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.comap (blockLinSubst e A).toRingHom) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«LinEmbed».«isMultiHomogIdeal_comap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomogIdeal_comap_a23a80c5c85c
