-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_hasFDerivAt_eval_7b0374bbcb50
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_hasFDerivAt_eval_7b0374bbcb50
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:02.104342+00:00
-- url     : https://prove2.me/theorems/aaae2f32-598a-41df-aef4-aa04f5d84150
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Good Point Chart has FDeriv At eval 7b0374bbcb50: P2 M Ground Theory Heights  Heights Normal Model Good Point Chart has FDeriv At eval 7b0374bbcb50
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Good Point Chart has FDeriv At eval 7b0374bbcb50 construction uses the P2 M Ground Theory Heights  Heights Normal Model Good Point Chart has FDeriv At eval 7b0374bbcb50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L11-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L11-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointChartLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
open MvPolynomial Topology
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_hasFDerivAt_eval_7b0374bbcb50 {σ : Type} [Fintype σ] [DecidableEq σ] (q : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun z : σ → ℂ => eval z q)
      (∑ j, eval x (pderiv j q) • ContinuousLinearMap.proj j : (σ → ℂ) →L[ℂ] ℂ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelGoodPointChart».«hasFDerivAt_eval» := P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_hasFDerivAt_eval_7b0374bbcb50
