-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_pair_main_term_above_2e18
-- name    : WeakGoldbach.symmetric_pair_main_term_above_2e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T22:44:21.143016+00:00
-- url     : https://prove2.me/theorems/dda1eab7-cf9d-4c6b-9db9-2339f4f6f944
-- title:
--   Hardy–Littlewood main-term bound for symmetric prime pairs
-- statement:
--   For every natural number $m > 2\cdot 10^{18}$, the number of symmetric prime offsets satisfies
--
--   $$
--   R(m) \;\ge\; \mathfrak{S}(2m)\,\frac{m}{\log^2 m},
--   \qquad
--   \mathfrak{S}(2m) = \prod_{\substack{p \mid 2m \\ p > 2}} \frac{p-1}{p-2}.
--   $$
--
--   This is the quantitative Hardy–Littlewood main-term bound for the binary Goldbach representation count — the genuine analytic content of the conjecture: the circle method predicts $R(m) \sim 2C_2\,\mathfrak{S}(2m)\,\frac{2m}{\log^2 m}$, and a lower bound of this order would prove Goldbach. The local factor $\mathfrak{S}$ is the $n$-dependent part of the singular series (it is $\ge 1$; the universal factor $2C_2 \approx 1.32$ is absorbed into the bound).
-- source:
--   Hardy–Littlewood main term for binary Goldbach representations

import Mathlib

namespace WeakGoldbach

theorem symmetric_pair_main_term_above_2e18 (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) / (Real.log m) ^ 2
      ≤ ((Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  sorry

end WeakGoldbach
