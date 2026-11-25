-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymDelta_mul_vanishes_02d963608782
-- name    : P2M_GroundTheory_Heights__Heights_antisymDelta_mul_vanishes_02d963608782
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:02.908803+00:00
-- url     : https://prove2.me/theorems/a7936c7c-0159-40d8-aa8e-9cf9986a4d09
-- title:
--   P2 M Ground Theory Heights  Heights antisym Delta mul vanishes 02d963608782: P2 M Ground Theory Heights  Heights antisym Delta mul vanishes 02d963608782
-- statement:
--   The P2 M Ground Theory Heights  Heights antisym Delta mul vanishes 02d963608782 construction uses the P2 M Ground Theory Heights  Heights antisym Delta mul vanishes 02d963608782 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L114-L120

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

theorem P2M_GroundTheory_Heights__Heights_antisymDelta_mul_vanishes_02d963608782 (T : Type*) [Fintype T] [DecidableEq T] (N j : ℕ)
    (l : MvPolynomial (T × Fin N) ℝ) (τ : T) (a b : Fin N) (ha : a.val < j) (hb : j ≤ b.val) :
    ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
      ∀ x ∈ O ∩ diagHyperplane T N τ a b, eval x (antisymDelta T N * l) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«antisymDelta_mul_vanishes» := P2M_GroundTheory_Heights__Heights_antisymDelta_mul_vanishes_02d963608782
