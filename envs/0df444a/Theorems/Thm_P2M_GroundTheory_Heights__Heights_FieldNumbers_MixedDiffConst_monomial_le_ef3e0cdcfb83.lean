-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_le_ef3e0cdcfb83
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_le_ef3e0cdcfb83
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:13.142824+00:00
-- url     : https://prove2.me/theorems/e6895c17-0f25-5edf-89bc-01d1b4cccbda
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial le ef3e0cdcfb83: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial le ef3e0cdcfb83
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial le ef3e0cdcfb83 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const monomial le ef3e0cdcfb83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L70-L72

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_le_ef3e0cdcfb83 (p : MvPolynomial K ℚ) {v : K →₀ ℕ} (hv : v ∈ p.support) :
    (monomial v (coeff v p)).totalDegree ≤ p.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«monomial_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_le_ef3e0cdcfb83
