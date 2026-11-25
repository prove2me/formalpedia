-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_polyStep_deg_d254c2915618
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_polyStep_deg_d254c2915618
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:08.415802+00:00
-- url     : https://prove2.me/theorems/99647edd-32d5-4f7c-b9ea-24e13b5e8f47
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const poly Step deg d254c2915618: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const poly Step deg d254c2915618
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const poly Step deg d254c2915618 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const poly Step deg d254c2915618 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L74-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_polyStep_deg_d254c2915618 (b : K → ℤ) (p : MvPolynomial K ℚ) :
    polyStep b p = 0 ∨ (polyStep b p).totalDegree + 1 ≤ p.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«polyStep_deg» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_polyStep_deg_d254c2915618
