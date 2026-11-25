-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ineq_self_0ba56674a6fa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ineq_self_0ba56674a6fa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:52.914584+00:00
-- url     : https://prove2.me/theorems/b313b841-cbbb-5c24-b0b5-26ae92f4c734
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ineq self 0ba56674a6fa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ineq self 0ba56674a6fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ineq self 0ba56674a6fa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ineq self 0ba56674a6fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L524-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L524-L532

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (polyMax Mollifier molli regMax coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart maMeasure)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
open ReciprocityTheory.AnForm.M

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ineq_self_0ba56674a6fa (M t H : ℝ) (hM : 0 ≤ M) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 4) (h : -M ≤ H) :
    -(2 * M * (13 / 4) ^ 2) * (2 * (1 + t) ^ 2)⁻¹ ≤ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«ineq_self» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ineq_self_0ba56674a6fa
