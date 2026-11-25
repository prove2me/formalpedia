-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_le_ker_genericEvaluation_940d81026d18
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_le_ker_genericEvaluation_940d81026d18
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:35.390674+00:00
-- url     : https://prove2.me/theorems/58a0d178-84e1-4bc6-80e3-4c9e4055c29e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map le ker generic Evaluation 940d81026d18: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map le ker
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map le ker generic Evaluation 940d81026d18 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map le ker generic Evaluation 940d81026d18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L129-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_le_ker_genericEvaluation_940d81026d18 (P : Ideal (MRing ι)) :
    Ideal.map (rename Sum.inr) P ≤ RingHom.ker (genericEvaluation (S := S) P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«map_le_ker_genericEvaluation» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_le_ker_genericEvaluation_940d81026d18
