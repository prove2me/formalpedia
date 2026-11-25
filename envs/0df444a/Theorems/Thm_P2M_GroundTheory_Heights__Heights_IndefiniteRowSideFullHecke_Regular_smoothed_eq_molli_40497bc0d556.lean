-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_smoothed_eq_molli_40497bc0d556
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_smoothed_eq_molli_40497bc0d556
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:21.948842+00:00
-- url     : https://prove2.me/theorems/c28bb137-ea75-4501-9672-eca2e50d6509
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular smoothed eq molli 40497bc0d556: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular smoothed eq molli
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular smoothed eq molli 40497bc0d556 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular smoothed eq molli 40497bc0d556 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L150-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L150-L175

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_smoothed_eq_molli_40497bc0d556 (R : RegChartDataA A) (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N)
    (z : Fin D → ℂ) (ht : 0 < t) (hK : ∀ y ∈ ball z t, y ∉ coordDiv (R.S j) → -K ≤ R.u j y) :
    R.smoothed ρ K t j z = molli ρ t (R.u j) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«smoothed_eq_molli» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_smoothed_eq_molli_40497bc0d556
