-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_75k
-- name    : TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_75k
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:07:11.740672+00:00
-- url     : https://prove2.me/theorems/3435f395-db12-439d-9db4-b689c09f07be
-- title:
--   Chebyshev psi error in the middle range from RH through height 75,000
-- statement:
--   Assume that every zero of the Riemann zeta function in the open critical strip with imaginary part between $0$ and $75{,}000$ lies on the critical line. Then, for every real $y$ with $e^{23}\le y<e^{136}$,
--
--   $$
--   |\psi(y)-y|\le\frac{y}{40\log y}.
--   $$
--
--   This strengthens the earlier conditional middle-range reduction, which assumed the corresponding zero verification through height $100{,}000$. It does not assert that the finite-height hypothesis is proved.
-- source:
--   Refinement of the accepted double-smoothing and finite-height RH reduction https://prove2.me/submissions/abf2274f-caaf-476f-9e2e-b84896edbc3d. The zero sum, reciprocal bounds and 7/8 zero-free input are separate proved Prove2Me results; the 7/8 input comes from OpenAI math, https://github.com/openai/math/blob/main/lean/docs/003.md.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Exp

theorem TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_75k
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 75000 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
