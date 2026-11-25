-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chart_congr_3df726d03254
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chart_congr_3df726d03254
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:40.613009+00:00
-- url     : https://prove2.me/theorems/0c3f81ce-3460-4295-a8e1-ccbe57545e2b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chart congr 3df726d03254: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chart congr 3df726d03254
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chart congr 3df726d03254 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin chart congr 3df726d03254 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankAdjoin.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankAdjoin.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chart_congr_3df726d03254 {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankAdjoin».«chart_congr» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_chart_congr_3df726d03254
