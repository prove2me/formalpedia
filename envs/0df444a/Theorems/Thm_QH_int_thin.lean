-- Prove2me | Theorems.Thm_QH_int_thin
-- name    : QH.int_thin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:42.746747+00:00
-- url     : https://prove2.me/theorems/9076b3b8-4029-52f2-a333-8890a1728e9d
-- title:
--   QH: int thin
-- statement:
--   The QH construction uses the int thin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/IntThin.lean#L169-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/IntThin.lean#L169-L262

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_ZeroFreeRegionGl2PrimeChoiceResults
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_IntThin
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

theorem QH.int_thin :
    ∀ ε c C A c' : ℝ, 0 < ε → 0 < c → 0 < C → 0 < A → 0 < c' → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (y lam : ℝ) (φ : ℝ → ℂ),
      Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ A * x ^ (ε / 5) * Real.log x ^ 2 →
      (∀ u : ℝ, y ≤ u → ‖φ u‖ ≤ C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
      ‖(y : ℂ) * ∫ u in Set.Ioi y, φ u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-(c' * x ^ (ε / 8))) := by sorry
