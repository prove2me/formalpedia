-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_indicator_mul_ac02c5b20e31
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_indicator_mul_ac02c5b20e31
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:35.096411+00:00
-- url     : https://prove2.me/theorems/c72fd66d-7e62-4ea3-86dd-95dbd5a64e80
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add indicator mul ac02c5b20e31: P2 M Ground Theory Heights  Heights Chart Int Count Add indicator mul ac02c5b20e31
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add indicator mul ac02c5b20e31 construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add indicator mul ac02c5b20e31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L76-L78

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_indicator_mul_ac02c5b20e31 (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    S.indicator f x * c = S.indicator (fun z => f z * c) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«indicator_mul» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_indicator_mul_ac02c5b20e31
