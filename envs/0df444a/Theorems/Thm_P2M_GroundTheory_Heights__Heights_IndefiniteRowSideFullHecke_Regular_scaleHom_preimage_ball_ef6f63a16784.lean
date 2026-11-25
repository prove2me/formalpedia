-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_preimage_ball_ef6f63a16784
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_preimage_ball_ef6f63a16784
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:47.341803+00:00
-- url     : https://prove2.me/theorems/7539cb07-5e15-495c-ba43-307f2f2b0ebf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular scale Hom preimage ball ef6f63a16784: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular scale Hom pr
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular scale Hom preimage ball ef6f63a16784 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular scale Hom preimage ball ef6f63a16784 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartsOfRegCharts.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedChartsOfRegCharts.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_preimage_ball_ef6f63a16784 (D : ℕ) {c : ℝ} (hc : 0 < c) :
    scaleHom D hc ⁻¹' ball 0 c ⊆ ball 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«scaleHom_preimage_ball» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_scaleHom_preimage_ball_ef6f63a16784
