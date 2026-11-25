-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled___86efd14e079c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled___86efd14e079c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:41.714911+00:00
-- url     : https://prove2.me/theorems/f2ab30af-042b-4076-aa22-9270e9711446
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scaled   86efd14e079c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scale
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scaled   86efd14e079c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scaled   86efd14e079c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartsOfRegCharts.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartsOfRegCharts.lean#L107-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StBoundedChartsOfRegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartsOfRegCharts
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
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
variable (R : RegCharts A) (M : Fin R.n → ℝ) (hM0 : ∀ j, 0 < M j)
  (hM : ∀ j, closure (R.W' j) ⊆ ball 0 (M j))

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled___86efd14e079c : (R.scaled M hM0 hM).θ = R.θ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«RegCharts».«scaled_θ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled___86efd14e079c
