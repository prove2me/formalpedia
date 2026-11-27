-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_glued_eq_regularised_5d0a982dd854
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_glued_eq_regularised_5d0a982dd854
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:07:36.722796+00:00
-- url     : https://prove2.me/theorems/9bc64e6a-79c1-52be-a31d-b8c036c22f77
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular glued eq regularised 5d0a982dd854: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular glued eq regula
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular glued eq regularised 5d0a982dd854 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular glued eq regularised 5d0a982dd854 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L217-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L217-L234

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_glued_eq_regularised_5d0a982dd854 [T2Space X] (R : RegChartData A) (hW : ∀ j, R.W j ⊆ ball 0 1)
    (hf : ∀ j, ContDiffOn ℝ ∞ (R.f j) (R.W j)) (ρ : Mollifier D) (K : ℝ) (η : Fin R.n → X → ℝ)
    (C t : ℝ) (x : X) (hε : 0 ≤ errorWithLinear C t)
    (hmol : ∀ j, x ∈ R.V' j → (R.toRegular hW hf).phReg ρ K t j x = R.phChart R.φ ρ t j x) :
    R.glued R.φ ρ η C t x = (R.toRegular hW hf).regularised ρ K t (errorWithLinear C t) η x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«glued_eq_regularised» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_glued_eq_regularised_5d0a982dd854
