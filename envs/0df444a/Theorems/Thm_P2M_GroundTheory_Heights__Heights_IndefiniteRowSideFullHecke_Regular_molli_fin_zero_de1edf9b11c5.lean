-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_molli_fin_zero_de1edf9b11c5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_molli_fin_zero_de1edf9b11c5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:46.852915+00:00
-- url     : https://prove2.me/theorems/741ef4ac-a65a-4476-a3de-cb165da9e248
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular molli fin zero de1edf9b11c5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular molli fin zero de1edf
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular molli fin zero de1edf9b11c5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular molli fin zero de1edf9b11c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L246-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L246-L255

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_molli_fin_zero_de1edf9b11c5 (ρ : Mollifier 0) (t : ℝ) (f : (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) :
    molli ρ t f z = f z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«molli_fin_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_molli_fin_zero_de1edf9b11c5
