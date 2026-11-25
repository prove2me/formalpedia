-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_crdj_symm_self_9ea9178b0602
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_crdj_symm_self_9ea9178b0602
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:47.943142+00:00
-- url     : https://prove2.me/theorems/1d62c363-2dae-47d7-b12d-c9fdcaa602a4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular crdj symm self 9ea9178b0602: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular crdj symm self 9ea917
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular crdj symm self 9ea9178b0602 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular crdj symm self 9ea9178b0602 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L396-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L396-L399

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_crdj_symm_self_9ea9178b0602 (j : Fin 2) (y : Fin 1 → ℂ) : crdj j ((p1.chart j).symm y) = y 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«crdj_symm_self» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_crdj_symm_self_9ea9178b0602
