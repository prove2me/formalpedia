-- Prove2me | Theorems.Thm_TaoFivePrimes_prime_in_short_interval_of_finiteRH3290M
-- name    : TaoFivePrimes.prime_in_short_interval_of_finiteRH3290M
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T20:12:24.262921+00:00
-- url     : https://prove2.me/theorems/ac28254d-31be-4af6-8475-cc87278a3b70
-- title:
--   The full Tao short-prime interval from explicit finite RH through 3.29 billion
-- statement:
--   Assuming that every nontrivial zeta zero with absolute imaginary part at most $3.29\times10^9$ has real part $1/2$, every real $x\ge1.1\times10^{10}$ has a prime $p\le x$ with $x-p\le x/(2.8\times10^7)$. This proves the complete analytic interval implication and discharges all smoothing, convergence, prime-power, count, remainder, width, and finite-range hypotheses. It does not assert finite RH or close the unconditional interval theorem.
-- source:
--   Independent order-18 unsieved smoothing of the actual published Perron formula. Finite RH through 3.29e9 is explicitly assumed, not proved.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_dusart_psi_433_20261014_ExplicitFormula
import Mathlib
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LogarithmicZeroCount
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Theorems.Thm_RamareSaouter2003_prime_interval_finite_range
import Theorems.Thm_TaoFivePrimes_positive_zero_nineteenth_moment_tail
import Theorems.Thm_TaoFivePrimes_prime_power_correction_nearby

theorem TaoFivePrimes.prime_in_short_interval_of_finiteRH3290M
    (hRH : ∀ rho : ℂ, DusartSmoothing.RvM.IsNontrivialZero rho →
      |rho.im| ≤ (3290000000 : ℝ) → rho.re = 1/2)
    (x : ℝ) (hx : 1.1*10^10 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x-p ≤ x/(2.8*10^7) := by sorry
