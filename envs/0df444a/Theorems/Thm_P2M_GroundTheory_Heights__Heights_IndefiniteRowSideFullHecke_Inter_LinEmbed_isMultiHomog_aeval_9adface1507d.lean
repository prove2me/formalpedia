-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_aeval_9adface1507d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_aeval_9adface1507d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:30.509123+00:00
-- url     : https://prove2.me/theorems/4b01aec7-d32f-5de7-8ab4-c3f2d00b6d4b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Multi Homog aeval 9adface1507d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Multi Homog aeval 9adface1507d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Lin Embed is Multi Homog aeval 9adface1507d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean#L43-L65

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
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')]
open Classical

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_aeval_9adface1507d (τ : K ≃ K') (g : (Σ k, ι k) → MRingOver F ι')
    (hg : ∀ p, IsMultiHomog (g p) (Pi.single (τ p.1) 1)) {s : MRingOver F ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) : IsMultiHomog (aeval g s) (a ∘ τ.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«LinEmbed».«isMultiHomog_aeval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_aeval_9adface1507d
