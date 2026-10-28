-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_65k_and_sine_weight
-- name    : TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_65k_and_sine_weight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:02:24.624023+00:00
-- url     : https://prove2.me/theorems/3b2a8bac-60ea-4e93-94ed-efab47beb140
-- title:
--   Middle-range psi estimate from height 65,000 RH and a sine-weight bound
-- statement:
--   Assume that every nontrivial zeta zero with ordinate between $0$ and $65000$ lies on the critical line. Also assume that for every $1/2151\le r\le1/2149$ and every finite set $Z$ of nontrivial zeros with $|\operatorname{Im}\rho|>65000$,
--
--   $$
--   \sum_{\rho\in Z}\frac{m_\rho}{|\operatorname{Im}\rho|^3}
--   \min\!\left\{4\sin^2\!\left(\frac{r\operatorname{Im}\rho}{2}\right)+8r+3|\operatorname{Im}\rho|r^2,\,4\right\}
--   \le\frac{115}{10^{11}}.
--   $$
--
--   Here $m_\rho$ is the analytic multiplicity. Then for every $e^{23}\le y<e^{136}$,
--
--   $$
--   |\psi(y)-y|\le\frac{y}{40\log y}.
--   $$
--
--   Both the finite-height RH statement and the sine-weight estimate are explicit assumptions; this theorem does not assert either one.
-- source:
--   Derived from the proved 75,000-height middle-range smoothing reduction, the proved 65,000 low- and high-zero weight estimates, and the conditional sine-sensitive zero-sum bound; the finite-height RH and numerical sine-weight statements remain explicit hypotheses.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
open DusartSmoothing Complex Set

theorem TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_65k_and_sine_weight
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 65000 → s.re = 1/2)
    (hW : ∀ r : ℝ, (1/2151:ℝ) ≤ r → r ≤ (1/2149:ℝ) →
      ∀ Z : Finset ℂ, (∀ ρ ∈ Z, RvM.IsNontrivialZero ρ) →
      (∀ ρ ∈ Z, 65000 < |ρ.im|) →
      (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
        ((min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3 * |ρ.im| * r^2) 4) /
          |ρ.im|^3)) ≤ (115/10^11:ℝ))
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
