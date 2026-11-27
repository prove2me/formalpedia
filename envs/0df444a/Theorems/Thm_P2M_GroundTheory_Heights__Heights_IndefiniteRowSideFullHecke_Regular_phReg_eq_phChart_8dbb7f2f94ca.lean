-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_eq_phChart_8dbb7f2f94ca
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_eq_phChart_8dbb7f2f94ca
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:14.815866+00:00
-- url     : https://prove2.me/theorems/9e18f3b0-316e-4d87-8ffb-a796f2d2cbd7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg eq ph Chart 8dbb7f2f94ca: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg eq ph Char
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg eq ph Chart 8dbb7f2f94ca construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Reg eq ph Chart 8dbb7f2f94ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L177-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L177-L184

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_eq_phChart_8dbb7f2f94ca [CompactSpace X] (R : RegChartDataA A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N)
    (x : X) (ht : 0 < t)
    (hK : ∀ y ∈ ball (R.chart j x) t, y ∉ coordDiv (R.S j) → -K ≤ R.u j y) :
    R.phReg ρ K t j x = (RegChartData.ofRegular R om om_pot om_pos).phChart R.ph ρ t j x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«phReg_eq_phChart» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_eq_phChart_8dbb7f2f94ca
