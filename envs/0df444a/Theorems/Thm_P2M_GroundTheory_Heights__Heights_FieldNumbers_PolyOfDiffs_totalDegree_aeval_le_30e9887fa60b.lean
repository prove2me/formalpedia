-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:48.276384+00:00
-- url     : https://prove2.me/theorems/4e80890a-e3f8-40d5-9cfc-bb296f049469
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree aeval le 30e9887fa60b: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree aeval le 30e9887fa60b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree aeval le 30e9887fa60b construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs total Degree aeval le 30e9887fa60b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L13-L23

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b (g : K → MvPolynomial K ℚ) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (P : MvPolynomial K ℚ) : (aeval g P).totalDegree ≤ P.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«totalDegree_aeval_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b
