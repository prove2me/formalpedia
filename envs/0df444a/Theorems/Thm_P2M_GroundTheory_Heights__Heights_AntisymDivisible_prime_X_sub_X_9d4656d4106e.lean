-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_prime_X_sub_X_9d4656d4106e
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_prime_X_sub_X_9d4656d4106e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:15.23888+00:00
-- url     : https://prove2.me/theorems/3ddc5814-5131-417d-be4a-5bee732624a6
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible prime X sub X 9d4656d4106e: P2 M Ground Theory Heights  Heights Antisym Divisible prime X sub X 9d4656d4106e
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible prime X sub X 9d4656d4106e construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible prime X sub X 9d4656d4106e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L54-L71

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
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_prime_X_sub_X_9d4656d4106e {u v : σ} (huv : u ≠ v) : Prime (X u - X v : MvPolynomial σ ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«prime_X_sub_X» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_prime_X_sub_X_9d4656d4106e
