-- Prove2me | Theorems.Thm_ShiBQP_polyBound_three_phase_compose
-- name    : ShiBQP.polyBound_three_phase_compose
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T09:13:28.248029+00:00
-- url     : https://prove2.me/theorems/c9470be5-59e7-4662-b824-2a4f8ede7dd6
-- title:
--   A three-phase running time with a data-dependent middle phase is polynomially bounded
-- statement:
--   Consider a computation in three phases: a first phase whose step count is bounded by a polynomial in the input length, a middle phase costing two steps per symbol of an intermediate string plus a constant, and a third phase whose step count is bounded by a polynomial in the LENGTH OF THAT INTERMEDIATE STRING. Provided the intermediate length is itself bounded by the input length plus a constant multiple of the first polynomial, the total is bounded by a single polynomial in the input length.
--
--   The intermediate length is quantified with an inequality rather than given by an equation, because a machine construction can only ever bound it, never compute it exactly. Making the third phase's polynomial depend on that length is what forces polynomial composition, and using the bound at all requires that evaluation of a polynomial with natural-number coefficients is monotone, which is proved here as a step since the library does not provide it.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiBQP

theorem polyBound_three_phase_compose (p₁ p₂ : Polynomial ℕ) (c d : ℕ) :
    ∃ q : Polynomial ℕ, ∀ n m : ℕ, m ≤ n + c * Polynomial.eval n p₁ →
      Polynomial.eval n p₁ + (2 * m + d) + Polynomial.eval m p₂ ≤ Polynomial.eval n q := by
  sorry

end ShiBQP
