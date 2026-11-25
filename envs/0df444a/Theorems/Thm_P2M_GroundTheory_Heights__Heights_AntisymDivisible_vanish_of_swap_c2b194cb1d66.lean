-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_swap_c2b194cb1d66
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_swap_c2b194cb1d66
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:20.841391+00:00
-- url     : https://prove2.me/theorems/9b5cb64b-79ca-4098-9418-64f641afd406
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible vanish of swap c2b194cb1d66: P2 M Ground Theory Heights  Heights Antisym Divisible vanish of swap c2b194cb1d66
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible vanish of swap c2b194cb1d66 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible vanish of swap c2b194cb1d66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L87-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L87-L100

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

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_swap_c2b194cb1d66 (u v : σ) (P : MvPolynomial σ ℝ) (h : rename (Equiv.swap u v) P = -P) :
    ∀ x : σ → ℝ, x u = x v → eval x P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«vanish_of_swap» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_swap_c2b194cb1d66
