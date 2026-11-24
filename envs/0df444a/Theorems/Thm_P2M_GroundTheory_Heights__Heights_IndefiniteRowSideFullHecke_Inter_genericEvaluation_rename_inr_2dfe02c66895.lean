-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericEvaluation_rename_inr_2dfe02c66895
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericEvaluation_rename_inr_2dfe02c66895
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:01.827806+00:00
-- url     : https://prove2.me/theorems/812c677d-66a0-4e64-8305-a17050f6017c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Evaluation rename inr 2dfe02c66895: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Ev
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Evaluation rename inr 2dfe02c66895 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Evaluation rename inr 2dfe02c66895 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L89-L91

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericEvaluation_rename_inr_2dfe02c66895 (P : Ideal (MRing ι)) (f : MRing ι) :
    genericEvaluation (S := S) P (rename Sum.inr f) = C (toFn P f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«genericEvaluation_rename_inr» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericEvaluation_rename_inr_2dfe02c66895
