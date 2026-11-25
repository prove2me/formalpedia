-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genericEvaluation_le_c256039eadb2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genericEvaluation_le_c256039eadb2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:26.325807+00:00
-- url     : https://prove2.me/theorems/e1152a2b-338d-4b9a-8caf-c7bb13c921c3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker generic Evaluation le c256039eadb2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker generic Ev
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker generic Evaluation le c256039eadb2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker generic Evaluation le c256039eadb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L108-L125

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genericEvaluation_le_c256039eadb2 (P : Ideal (MRing ι)) :
    RingHom.ker (genericEvaluation (S := S) P) ≤ Ideal.map (rename Sum.inr) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«ker_genericEvaluation_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genericEvaluation_le_c256039eadb2
