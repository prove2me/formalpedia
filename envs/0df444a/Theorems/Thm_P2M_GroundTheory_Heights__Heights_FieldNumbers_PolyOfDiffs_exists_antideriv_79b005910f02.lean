-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:38.447404+00:00
-- url     : https://prove2.me/theorems/388f10f9-97f5-42ca-b57c-9bdaa5f8dc6b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists antideriv 79b005910f02: P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists antideriv 79b005910f02
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists antideriv 79b005910f02 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Poly Of Diffs exists antideriv 79b005910f02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L54-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPolyOfDiffs.lean#L54-L98

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02 (k : K) (q : MvPolynomial K ℚ) : ∃ P : MvPolynomial K ℚ,
    P.totalDegree ≤ q.totalDegree + 1 ∧
    ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PolyOfDiffs».«exists_antideriv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02
