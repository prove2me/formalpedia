-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:53.24359+00:00
-- url     : https://prove2.me/theorems/877ed81e-743c-4f42-bb89-7ba382a60730
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise abs half log le 044daed9760d: P2 M Ground Theory Heights  Heights Lelong Regularise abs half log le 044daed9760d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise abs half log le 044daed9760d construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise abs half log le 044daed9760d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L48-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L48-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (t ^ 2 + ε) / 2| ≤ |Real.log t| + |Real.log (2 * t)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«abs_half_log_le» := P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d
