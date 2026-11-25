-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_pow_antideriv_69ad4af11f37
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_pow_antideriv_69ad4af11f37
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:08.261326+00:00
-- url     : https://prove2.me/theorems/ae7e2d92-c83b-5adc-8608-f16379e80c05
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists pow antideriv 69ad4af11f37: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists pow antideriv 69ad4af11f37
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists pow antideriv 69ad4af11f37 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists pow antideriv 69ad4af11f37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L27-L45

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_pow_antideriv_69ad4af11f37 (a : ℕ) : ∃ F : Polynomial ℚ, F.natDegree ≤ a + 1 ∧
    ∀ x : ℚ, F.eval x - F.eval (x - 1) = x ^ a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«exists_pow_antideriv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_pow_antideriv_69ad4af11f37
