-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_freeze_le_431705d6eba7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_freeze_le_431705d6eba7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:37.039975+00:00
-- url     : https://prove2.me/theorems/7a79f4e2-9088-4e67-b6d8-6d50a6244fc9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree freeze le 431705d6eba7: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree freeze le 431705d6eba7
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree freeze le 431705d6eba7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree freeze le 431705d6eba7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L103-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_freeze_le_431705d6eba7 (s : Finset K) (N : K → ℚ) (j : K) :
    (freeze s N j).totalDegree ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«totalDegree_freeze_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_freeze_le_431705d6eba7
