-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_coeff_le_sum_abs_coeff_f3bc80b28092
-- name    : P2M_GroundTheory_Heights__Heights_abs_coeff_le_sum_abs_coeff_f3bc80b28092
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:46.027798+00:00
-- url     : https://prove2.me/theorems/55dc1774-5083-491b-9b73-c538589e8bb8
-- title:
--   P2 M Ground Theory Heights  Heights abs coeff le sum abs coeff f3bc80b28092: P2 M Ground Theory Heights  Heights abs coeff le sum abs coeff f3bc80b28092
-- statement:
--   The P2 M Ground Theory Heights  Heights abs coeff le sum abs coeff f3bc80b28092 construction uses the P2 M Ground Theory Heights  Heights abs coeff le sum abs coeff f3bc80b28092 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_abs_coeff_le_sum_abs_coeff_f3bc80b28092 {σ : Type*} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m p| ≤ ∑ m' ∈ p.support, |coeff m' p| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«abs_coeff_le_sum_abs_coeff» := P2M_GroundTheory_Heights__Heights_abs_coeff_le_sum_abs_coeff_f3bc80b28092
