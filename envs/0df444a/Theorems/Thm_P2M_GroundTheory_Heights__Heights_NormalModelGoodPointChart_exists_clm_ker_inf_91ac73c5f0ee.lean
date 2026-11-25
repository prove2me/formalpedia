-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_clm_ker_inf_91ac73c5f0ee
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_clm_ker_inf_91ac73c5f0ee
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:06.597594+00:00
-- url     : https://prove2.me/theorems/0c8847f1-6580-4e22-99ca-1d851a99b0c6
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists clm ker inf 91ac73c5f0ee: P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists clm ker inf 91ac73c5f0ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists clm ker inf 91ac73c5f0ee construction uses the P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists clm ker inf 91ac73c5f0ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L53-L69

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

theorem P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_clm_ker_inf_91ac73c5f0ee {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (L : E →ₗ[ℂ] F) (hL : Function.Surjective L) (d : ℕ)
    (hd : Module.finrank ℂ E = d + Module.finrank ℂ F) :
    ∃ A : E →L[ℂ] (Fin d → ℂ), ∀ v, A v = 0 → L v = 0 → v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelGoodPointChart».«exists_clm_ker_inf» := P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_clm_ker_inf_91ac73c5f0ee
