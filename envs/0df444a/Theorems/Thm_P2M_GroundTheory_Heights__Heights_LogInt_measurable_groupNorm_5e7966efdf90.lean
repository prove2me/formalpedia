-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:48.85921+00:00
-- url     : https://prove2.me/theorems/72ba5d32-60f5-4369-884a-f3b35588c093
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measurable group Norm 5e7966efdf90: P2 M Ground Theory Heights  Heights Log Int measurable group Norm 5e7966efdf90
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measurable group Norm 5e7966efdf90 construction uses the P2 M Ground Theory Heights  Heights Log Int measurable group Norm 5e7966efdf90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L85-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90 (h : HermNorm n) (i : Fin k) :
    Measurable fun u : Fin k × Fin n → ℂ => h.norm fun j => u (i, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurable_groupNorm» := P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90
