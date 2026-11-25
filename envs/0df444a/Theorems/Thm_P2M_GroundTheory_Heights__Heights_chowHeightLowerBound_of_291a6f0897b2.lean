-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHeightLowerBound_of_291a6f0897b2
-- name    : P2M_GroundTheory_Heights__Heights_chowHeightLowerBound_of_291a6f0897b2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:19.825844+00:00
-- url     : https://prove2.me/theorems/c4b70267-8a44-4921-9eba-0627908e21ad
-- title:
--   P2 M Ground Theory Heights  Heights chow Height Lower Bound of 291a6f0897b2: P2 M Ground Theory Heights  Heights chow Height Lower Bound of 291a6f0897b2
-- statement:
--   The P2 M Ground Theory Heights  Heights chow Height Lower Bound of 291a6f0897b2 construction uses the P2 M Ground Theory Heights  Heights chow Height Lower Bound of 291a6f0897b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L241-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L241-L312

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open Classical

theorem P2M_GroundTheory_Heights__Heights_chowHeightLowerBound_of_291a6f0897b2 (hR : ChowHeightRecursion.Statement) (hS : ChowFormSection.Statement)
    (hB : BaseChangeLogBound.Statement) (hMul : ChowHeightMul.Statement) :
    ChowHeightLowerBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chowHeightLowerBound_of» := P2M_GroundTheory_Heights__Heights_chowHeightLowerBound_of_291a6f0897b2
