-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
-- name    : P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:47.833791+00:00
-- url     : https://prove2.me/theorems/eb90a667-a622-4ffb-9248-cef0d8e865f6
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Sum Measurable is Closed zero Set b1e5ce62660e: P2 M Ground Theory Heights  Heights Sheet Sum Measurable is Closed zero Set b1e5ce62660e
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Sum Measurable is Closed zero Set b1e5ce62660e construction uses the P2 M Ground Theory Heights  Heights Sheet Sum Measurable is Closed zero Set b1e5ce62660e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetSumMeasurable.lean#L78-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
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
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetSumMeasurable».«isClosed_zeroSet» := P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
