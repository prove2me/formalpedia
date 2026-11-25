-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_swap_pair_f5c9f49b9aee
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_swap_pair_f5c9f49b9aee
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:33.961816+00:00
-- url     : https://prove2.me/theorems/bc07528a-bd8a-4b47-ab32-c6adebe186c8
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible swap pair f5c9f49b9aee: P2 M Ground Theory Heights  Heights Antisym Divisible swap pair f5c9f49b9aee
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible swap pair f5c9f49b9aee construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible swap pair f5c9f49b9aee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L196-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L196-L199

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

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_swap_pair_f5c9f49b9aee (τ : T) (a b i : Fin N) :
    Equiv.swap (τ, a) (τ, b) (τ, i) = (τ, Equiv.swap a b i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«swap_pair» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_swap_pair_f5c9f49b9aee
