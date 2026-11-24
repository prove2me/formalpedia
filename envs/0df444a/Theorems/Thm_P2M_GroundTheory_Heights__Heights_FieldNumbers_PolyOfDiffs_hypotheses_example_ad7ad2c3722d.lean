-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:21.876905+00:00
-- url     : https://prove2.me/theorems/e618e469-1034-4710-b062-cbab9dda5e66
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs hypotheses example ad7ad2c3722d: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs hypotheses example ad7ad2c3722d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs hypotheses example ad7ad2c3722d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs hypotheses example ad7ad2c3722d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L156-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d :
    ∀ k : Unit, ∃ q : MvPolynomial Unit ℚ, (q = 0 ∨ q.totalDegree < 1) ∧
      EventuallyPoly (diffStep (Pi.single k 1) (fun m : Unit → ℤ => m ())) q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«hypotheses_example» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d
