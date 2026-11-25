-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffLimit_proof_d38adac19914
-- name    : P2M_GroundTheory_Heights__Heights_CutOffLimit_proof_d38adac19914
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:53.157693+00:00
-- url     : https://prove2.me/theorems/10c5bec3-0e1a-4235-9efa-d9ad7c2d9942
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Limit proof d38adac19914: P2 M Ground Theory Heights  Heights Cut Off Limit proof d38adac19914
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Limit proof d38adac19914 construction uses the P2 M Ground Theory Heights  Heights Cut Off Limit proof d38adac19914 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffLimit.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffLimit.lean#L13-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffLimit
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

theorem P2M_GroundTheory_Heights__Heights_CutOffLimit_proof_d38adac19914 (hC : CutOff.Statement) (hM : ChartMassCompact.Statement)
    (hD : CutOffDominated.Statement) (hB : CutOffBoundaryBound.Statement) :
    CutOffLimit.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffLimit».«proof» := P2M_GroundTheory_Heights__Heights_CutOffLimit_proof_d38adac19914
