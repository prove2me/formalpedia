-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_toBoundedPsh_ph_f045e4f4b7be
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_toBoundedPsh_ph_f045e4f4b7be
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:35.132274+00:00
-- url     : https://prove2.me/theorems/67d2af63-55f5-4170-9614-d87d3a537f40
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bounded Th Psh to Bounded Psh ph f045e4f4b7be: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bou
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bounded Th Psh to Bounded Psh ph f045e4f4b7be construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bounded Th Psh to Bounded Psh ph f045e4f4b7be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L145-L146

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.BoundedThPsh

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_toBoundedPsh_ph_f045e4f4b7be [T2Space X] {R : RegCharts A} (P : BoundedThPsh R)
    (hW : ∀ j, R.W j ⊆ ball 0 1) : (P.toBoundedPsh hW).ph = P.φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«BoundedThPsh».«toBoundedPsh_ph» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_toBoundedPsh_ph_f045e4f4b7be
