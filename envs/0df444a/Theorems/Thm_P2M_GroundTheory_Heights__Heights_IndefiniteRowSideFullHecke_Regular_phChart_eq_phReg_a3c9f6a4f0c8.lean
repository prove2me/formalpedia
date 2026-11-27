-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phChart_eq_phReg_a3c9f6a4f0c8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phChart_eq_phReg_a3c9f6a4f0c8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:43.1249+00:00
-- url     : https://prove2.me/theorems/bd6f9a75-fb33-49f3-bb4b-61ad5c38f74e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Chart eq ph Reg a3c9f6a4f0c8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Chart eq ph Re
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Chart eq ph Reg a3c9f6a4f0c8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular ph Chart eq ph Reg a3c9f6a4f0c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L186-L191

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phChart_eq_phReg_a3c9f6a4f0c8 [T2Space X] (R : RegChartData A) (hW : ∀ j, R.W j ⊆ ball 0 1)
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.n) (x : X)
    (ht : 0 < t) (hK : ∀ y ∈ ball (R.ψ j x) t, y ∉ coordDiv (R.S j) → -K ≤ R.u R.φ j y) :
    (R.toRegular hW hf).phReg ρ K t j x = R.phChart R.φ ρ t j x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«phChart_eq_phReg» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phChart_eq_phReg_a3c9f6a4f0c8
