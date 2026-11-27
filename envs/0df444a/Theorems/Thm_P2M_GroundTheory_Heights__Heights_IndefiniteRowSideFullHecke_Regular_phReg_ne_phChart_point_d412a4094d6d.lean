-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_ne_phChart_point_d412a4094d6d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_ne_phChart_point_d412a4094d6d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:21.632181+00:00
-- url     : https://prove2.me/theorems/0c0bc901-463b-4be1-9515-66a243d271f4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg ne ph Chart point d412a4094d6d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg ne p
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg ne ph Chart point d412a4094d6d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg ne ph Chart point d412a4094d6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L265-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L265-L274

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
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
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)
local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_ne_phChart_point_d412a4094d6d (ρ : Mollifier 0) (t : ℝ) :
    pointReg.phReg ρ (-1) t (0 : Fin 1) () = 1 ∧
      (RegChartData.ofRegular pointReg pointOm pointOm_pot pointOm_pos).phChart pointReg.ph ρ t (0 : Fin 1) () = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«phReg_ne_phChart_point» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_ne_phChart_point_d412a4094d6d
