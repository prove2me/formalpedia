-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regularised_eq_glued_b1e4b0abc427
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regularised_eq_glued_b1e4b0abc427
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:39.83539+00:00
-- url     : https://prove2.me/theorems/b8c2cd0a-923c-493c-9f8e-7ed98027b6b9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular regularised eq glued b1e4b0abc427: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular regularised eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular regularised eq glued b1e4b0abc427 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular regularised eq glued b1e4b0abc427 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L193-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L193-L215

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regularised_eq_glued_b1e4b0abc427 [CompactSpace X] (R : RegChartDataA A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) (ρ : Mollifier D) (K : ℝ)
    (η : Fin R.N → X → ℝ) (C t : ℝ) (x : X) (hε : 0 ≤ errorWithLinear C t)
    (hmol : ∀ j, x ∈ R.mid j →
      R.phReg ρ K t j x = (RegChartData.ofRegular R om om_pot om_pos).phChart R.ph ρ t j x) :
    R.regularised ρ K t (errorWithLinear C t) η x =
      (RegChartData.ofRegular R om om_pot om_pos).glued R.ph ρ η C t x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«regularised_eq_glued» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_regularised_eq_glued_b1e4b0abc427
