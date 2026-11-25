-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled_W_subset_cd3accf47d3b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled_W_subset_cd3accf47d3b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:31:34.242117+00:00
-- url     : https://prove2.me/theorems/5192df3f-343c-47a2-81a7-9fb8bccefaf8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scaled W subset cd3accf47d3b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Chart
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scaled W subset cd3accf47d3b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Reg Charts scaled W subset cd3accf47d3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartsOfRegCharts.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartsOfRegCharts.lean#L109-L110

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled_W_subset_cd3accf47d3b (j : Fin R.n) : (R.scaled M hM0 hM).W j ⊆ ball 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«RegCharts».«scaled_W_subset» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_RegCharts_scaled_W_subset_cd3accf47d3b
