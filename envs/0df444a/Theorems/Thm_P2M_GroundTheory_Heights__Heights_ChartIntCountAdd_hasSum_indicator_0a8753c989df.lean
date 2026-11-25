-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_indicator_0a8753c989df
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_indicator_0a8753c989df
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:06.260943+00:00
-- url     : https://prove2.me/theorems/41ce70d8-b585-4f69-adfc-d5dd271245c2
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum indicator 0a8753c989df: P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum indicator 0a8753c989df
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum indicator 0a8753c989df construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum indicator 0a8753c989df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L18-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_indicator_0a8753c989df {E : ℕ → Set (Fin n → ℂ)} (hE : Pairwise (Function.onFun Disjoint E))
    (g : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    HasSum (fun i => (E i).indicator g x) ((⋃ i, E i).indicator g x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«hasSum_indicator» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_indicator_0a8753c989df
