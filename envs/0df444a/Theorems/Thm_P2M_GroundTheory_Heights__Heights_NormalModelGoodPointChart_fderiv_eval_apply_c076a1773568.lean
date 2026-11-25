-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_fderiv_eval_apply_c076a1773568
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_fderiv_eval_apply_c076a1773568
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:11.322222+00:00
-- url     : https://prove2.me/theorems/0e495125-cd20-4dfc-9b7f-da8d99f07705
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Good Point Chart fderiv eval apply c076a1773568: P2 M Ground Theory Heights  Heights Normal Model Good Point Chart fderiv eval apply c076a1773568
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Good Point Chart fderiv eval apply c076a1773568 construction uses the P2 M Ground Theory Heights  Heights Normal Model Good Point Chart fderiv eval apply c076a1773568 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L48-L51

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

theorem P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_fderiv_eval_apply_c076a1773568 {σ : Type} [Fintype σ] [DecidableEq σ] (q : MvPolynomial σ ℂ) (x v : σ → ℂ) :
    fderiv ℂ (fun z : σ → ℂ => eval z q) x v = ∑ s, eval x (pderiv s q) * v s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelGoodPointChart».«fderiv_eval_apply» := P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_fderiv_eval_apply_c076a1773568
