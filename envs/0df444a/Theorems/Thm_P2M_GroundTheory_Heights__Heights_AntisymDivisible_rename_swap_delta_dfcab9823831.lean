-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_rename_swap_delta_dfcab9823831
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_rename_swap_delta_dfcab9823831
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:30.945884+00:00
-- url     : https://prove2.me/theorems/c37e1f4d-6595-4f34-893c-8eaddb877459
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible rename swap delta dfcab9823831: P2 M Ground Theory Heights  Heights Antisym Divisible rename swap delta dfcab9823831
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible rename swap delta dfcab9823831 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible rename swap delta dfcab9823831 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L207-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L207-L238

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

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_rename_swap_delta_dfcab9823831 (τ₀ : T) {a b : Fin N} (hab : a ≠ b) :
    rename (Equiv.swap (τ₀, a) (τ₀, b)) (antisymDelta T N) = -antisymDelta T N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«rename_swap_delta» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_rename_swap_delta_dfcab9823831
