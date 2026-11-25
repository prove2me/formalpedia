-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_hypIncl_mem_ball_c348fbc1b221
-- name    : P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_hypIncl_mem_ball_c348fbc1b221
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:21.105294+00:00
-- url     : https://prove2.me/theorems/6eed1bba-608a-4ad6-96d8-bec16774ae32
-- title:
--   P2 M Ground Theory Heights  Heights Polydisc Lelong Limit hyp Incl mem ball c348fbc1b221: P2 M Ground Theory Heights  Heights Polydisc Lelong Limit hyp Incl mem ball c348fbc1b221
-- statement:
--   The P2 M Ground Theory Heights  Heights Polydisc Lelong Limit hyp Incl mem ball c348fbc1b221 construction uses the P2 M Ground Theory Heights  Heights Polydisc Lelong Limit hyp Incl mem ball c348fbc1b221 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolydiscLelongLimit.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolydiscLelongLimit.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ProjectiveLineZeroFormHolds
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolydiscLelongLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.PolydiscLelongLimit

theorem P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_hypIncl_mem_ball_c348fbc1b221 {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PolydiscLelongLimit».«hypIncl_mem_ball» := P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_hypIncl_mem_ball_c348fbc1b221
