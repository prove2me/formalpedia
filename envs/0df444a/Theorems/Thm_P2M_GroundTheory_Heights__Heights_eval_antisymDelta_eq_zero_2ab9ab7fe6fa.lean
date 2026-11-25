-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_antisymDelta_eq_zero_2ab9ab7fe6fa
-- name    : P2M_GroundTheory_Heights__Heights_eval_antisymDelta_eq_zero_2ab9ab7fe6fa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:52.523652+00:00
-- url     : https://prove2.me/theorems/57b2e6bf-58b8-49e5-869f-886b938aeae3
-- title:
--   P2 M Ground Theory Heights  Heights eval antisym Delta eq zero 2ab9ab7fe6fa: P2 M Ground Theory Heights  Heights eval antisym Delta eq zero 2ab9ab7fe6fa
-- statement:
--   The P2 M Ground Theory Heights  Heights eval antisym Delta eq zero 2ab9ab7fe6fa construction uses the P2 M Ground Theory Heights  Heights eval antisym Delta eq zero 2ab9ab7fe6fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L101-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
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

theorem P2M_GroundTheory_Heights__Heights_eval_antisymDelta_eq_zero_2ab9ab7fe6fa (T : Type*) [Fintype T] [DecidableEq T] (N : ℕ) {τ : T}
    {a b : Fin N} (hab : a < b) {x : T × Fin N → ℝ} (hx : x ∈ diagHyperplane T N τ a b) :
    eval x (antisymDelta T N) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_antisymDelta_eq_zero» := P2M_GroundTheory_Heights__Heights_eval_antisymDelta_eq_zero_2ab9ab7fe6fa
