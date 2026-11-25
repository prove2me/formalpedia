-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sliceIdeal_two_one_501a84e29669
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sliceIdeal_two_one_501a84e29669
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:32.745963+00:00
-- url     : https://prove2.me/theorems/4755781b-5f65-4ef7-b794-9a854a917af6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets slice Ideal two one 501a84e29669: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets slice
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets slice Ideal two one 501a84e29669 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets slice Ideal two one 501a84e29669 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PlaneIdealTwoOne.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PlaneIdealTwoOne.lean#L55-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PlaneIdealTwoOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sliceIdeal_two_one_501a84e29669 :
    planeIdeal 2 1 ⊔ Ideal.span {linForm (Pi.single (⟨0, by norm_num⟩ : Fin 2) (1 : ℂ)) - 1} =
      (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«sliceIdeal_two_one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sliceIdeal_two_one_501a84e29669
