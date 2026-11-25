-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_delta_factor_eq_det_6686b3b8ba3c
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_delta_factor_eq_det_6686b3b8ba3c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:33.347987+00:00
-- url     : https://prove2.me/theorems/0c96e3b8-2cd9-4265-8a43-0e0cdb0a2541
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible delta factor eq det 6686b3b8ba3c: P2 M Ground Theory Heights  Heights Antisym Divisible delta factor eq det 6686b3b8ba3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible delta factor eq det 6686b3b8ba3c construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible delta factor eq det 6686b3b8ba3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L201-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L201-L205

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
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
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_delta_factor_eq_det_6686b3b8ba3c (τ : T) :
    ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : MvPolynomial (T × Fin N) ℝ) =
      (Matrix.vandermonde (fun i : Fin N => (-X (τ, i) : MvPolynomial (T × Fin N) ℝ))).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«delta_factor_eq_det» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_delta_factor_eq_det_6686b3b8ba3c
