-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongLimit_proof_0051504eefea
-- name    : P2M_GroundTheory_Heights__Heights_LelongLimit_proof_0051504eefea
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:50.278011+00:00
-- url     : https://prove2.me/theorems/da18ad3d-c59f-46c2-a6a5-c9500089fa03
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Limit proof 0051504eefea: P2 M Ground Theory Heights  Heights Lelong Limit proof 0051504eefea
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Limit proof 0051504eefea construction uses the P2 M Ground Theory Heights  Heights Lelong Limit proof 0051504eefea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimit.lean#L35-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimit.lean#L35-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_LelongLimit_proof_0051504eefea (hOff : LelongLimitOffZero.Statement) (hOn : LelongLimitOnZero.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimit.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongLimit».«proof» := P2M_GroundTheory_Heights__Heights_LelongLimit_proof_0051504eefea
