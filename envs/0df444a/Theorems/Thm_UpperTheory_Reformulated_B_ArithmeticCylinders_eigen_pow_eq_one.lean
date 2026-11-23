-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ArithmeticCylinders_eigen_pow_eq_one
-- name    : UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:37.230002+00:00
-- url     : https://prove2.me/theorems/f7338d5a-8f46-4bf6-8fc9-e6d71655a8a0
-- title:
--   Arithmetic Cylinders: eigen pow eq one
-- statement:
--   The Arithmetic Cylinders construction uses the eigen pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ArithmeticCylinders.lean#L3-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ArithmeticCylinders.lean#L3-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ArithmeticCylinders
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one :
    ∀ {L : Type} [inst : Field L] {d : Type} [inst_1 : Fintype d] [inst_2 : DecidableEq d]
    (M : Matrix d d L) (n : ℕ), M ^ n = (1 : Matrix d d L) → ∀ (μ : L), M.charpoly.IsRoot μ → μ ^ n = (1 : L) := by sorry
