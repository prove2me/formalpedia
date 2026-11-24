-- Prove2me | Theorems.Thm_QH_small_zeros
-- name    : QH.small_zeros
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:48:19.498079+00:00
-- url     : https://prove2.me/theorems/b7d86a14-284b-4c7b-b70c-b7a798588a12
-- title:
--   QH: small zeros
-- statement:
--   The QH construction uses the small zeros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/SmallZeros.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/SmallZeros.lean#L32-L45

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SmallZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH

theorem QH.small_zeros :
    ∀ N₀ : ℕ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N ≤ N₀ → χ ≠ 1 → NoExc c₀ χ := by sorry
