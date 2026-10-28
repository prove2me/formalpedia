-- Prove2me | Theorems.Thm_TaoFivePrimes_sine_weight_high_zeros_65000
-- name    : TaoFivePrimes.sine_weight_high_zeros_65000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:10:09.691735+00:00
-- url     : https://prove2.me/theorems/6198611b-ccf3-4651-9594-7b097f1a4ee4
-- title:
--   Sine-sensitive weight of zeta zeros above height 65,000
-- statement:
--   Let $1/2151\le r\le1/2149$ and let $Z$ be a finite set of nontrivial zeta zeros with $|\operatorname{Im}\rho|>65000$. With analytic multiplicities $m_\rho$,
--
--   $$
--   \sum_{\rho\in Z}\frac{m_\rho}{|\operatorname{Im}\rho|^3}
--   \min\!\left\{4\sin^2\!\left(\frac{r\operatorname{Im}\rho}{2}\right)+8r+3|\operatorname{Im}\rho|r^2,\,4\right\}
--   \le\frac{115}{10^{11}}.
--   $$
--
--   The sum includes ordinates of both signs. This is an unconditional finite-set weight estimate; it does not assert that the zeros lie on the critical line.
-- source:
--   Derived from proved zero-count, sine-square interval, rational bin-weight, conjugation symmetry, and shifted reciprocal-cube tail certificates developed for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_TaoFivePrimes_SineBinData65k
import Definitions.Def_TaoFivePrimes_SineBinArithmetic65k
import Mathlib.Tactic
open DusartSmoothing Complex Set

theorem TaoFivePrimes.sine_weight_high_zeros_65000 (r : ℝ) (hr0 : (1/2151:ℝ) ≤ r) (hr1 : r ≤ (1/2149:ℝ))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, 65000 < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
      ((min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3 * |ρ.im| * r^2) 4) /
        |ρ.im|^3)) ≤ (115/10^11:ℝ) := by sorry
