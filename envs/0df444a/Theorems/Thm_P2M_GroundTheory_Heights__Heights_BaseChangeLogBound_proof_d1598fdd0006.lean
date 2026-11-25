-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_proof_d1598fdd0006
-- name    : P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_proof_d1598fdd0006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:35.193466+00:00
-- url     : https://prove2.me/theorems/ae41f62e-3244-42a3-86f7-c07a990345b5
-- title:
--   P2 M Ground Theory Heights  Heights Base Change Log Bound proof d1598fdd0006: P2 M Ground Theory Heights  Heights Base Change Log Bound proof d1598fdd0006
-- statement:
--   The P2 M Ground Theory Heights  Heights Base Change Log Bound proof d1598fdd0006 construction uses the P2 M Ground Theory Heights  Heights Base Change Log Bound proof d1598fdd0006 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBaseChangeLogBound.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBaseChangeLogBound.lean#L13-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBaseChangeLogBound
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
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_proof_d1598fdd0006 (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hC : ConeLogBound.Statement) : BaseChangeLogBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BaseChangeLogBound».«proof» := P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_proof_d1598fdd0006
