-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_uniform_coeff_bound_56e632b89056
-- name    : P2M_GroundTheory_Heights__Heights_exists_uniform_coeff_bound_56e632b89056
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:53.515457+00:00
-- url     : https://prove2.me/theorems/3fa06db6-a7d8-4131-87d6-daad43f65f41
-- title:
--   P2 M Ground Theory Heights  Heights exists uniform coeff bound 56e632b89056: P2 M Ground Theory Heights  Heights exists uniform coeff bound 56e632b89056
-- statement:
--   The P2 M Ground Theory Heights  Heights exists uniform coeff bound 56e632b89056 construction uses the P2 M Ground Theory Heights  Heights exists uniform coeff bound 56e632b89056 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean#L28-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean#L28-L50

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

theorem P2M_GroundTheory_Heights__Heights_exists_uniform_coeff_bound_56e632b89056 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : Type*} (G : E →ₗ[ℝ] MvPolynomial σ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : E) (m : σ →₀ ℕ), |coeff m (G y)| ≤ C * ‖y‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_uniform_coeff_bound» := P2M_GroundTheory_Heights__Heights_exists_uniform_coeff_bound_56e632b89056
