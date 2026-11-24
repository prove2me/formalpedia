-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949
-- name    : P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:18.666582+00:00
-- url     : https://prove2.me/theorems/732ba401-9554-4a8d-8bbb-f00b6f91ee94
-- title:
--   P2 M Ground Theory Heights  Heights cut Level mem 6f1a40581949: P2 M Ground Theory Heights  Heights cut Level mem 6f1a40581949
-- statement:
--   The P2 M Ground Theory Heights  Heights cut Level mem 6f1a40581949 construction uses the P2 M Ground Theory Heights  Heights cut Level mem 6f1a40581949 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLogLogCut.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLogLogCut.lean#L43-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
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
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949 (k : ℕ) : 0 < cutLevel k ∧ cutLevel k < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«cutLevel_mem» := P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949
