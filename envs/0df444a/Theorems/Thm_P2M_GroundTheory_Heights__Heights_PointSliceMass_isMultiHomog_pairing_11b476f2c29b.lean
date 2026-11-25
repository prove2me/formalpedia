-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointSliceMass_isMultiHomog_pairing_11b476f2c29b
-- name    : P2M_GroundTheory_Heights__Heights_PointSliceMass_isMultiHomog_pairing_11b476f2c29b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:11.97852+00:00
-- url     : https://prove2.me/theorems/d104abde-ae94-47bc-9b9d-ff56be5ba686
-- title:
--   P2 M Ground Theory Heights  Heights Point Slice Mass is Multi Homog pairing 11b476f2c29b: P2 M Ground Theory Heights  Heights Point Slice Mass is Multi Homog pairing 11b476f2c29b
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Slice Mass is Multi Homog pairing 11b476f2c29b construction uses the P2 M Ground Theory Heights  Heights Point Slice Mass is Multi Homog pairing 11b476f2c29b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPointSliceMass.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPointSliceMass.lean#L18-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointChowForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPointSliceMass
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointSliceMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointSliceMass_isMultiHomog_pairing_11b476f2c29b (y : Fin n → ℂ) :
    IsMultiHomog 1 (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointSliceMass».«isMultiHomog_pairing» := P2M_GroundTheory_Heights__Heights_PointSliceMass_isMultiHomog_pairing_11b476f2c29b
