-- Prove2me | Theorems.Thm_WeakGoldbach_singular_series_factor_ge_one
-- name    : WeakGoldbach.singular_series_factor_ge_one
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T22:44:25.677359+00:00
-- url     : https://prove2.me/theorems/adb05bba-c0aa-494e-ae8b-998130ef0f97
-- title:
--   The $n$-dependent singular-series factor is at least $1$
-- statement:
--   For every natural number $n$, the $n$-dependent part of the binary Goldbach singular series satisfies
--
--   $$
--   \mathfrak{S}(n) = \prod_{\substack{p \mid n \\ p > 2}} \frac{p-1}{p-2} \;\ge\; 1,
--   $$
--
--   since every local factor $(p-1)/(p-2) > 1$ for $p \ge 3$. This is the elementary component of the Hardy–Littlewood estimate: the singular series never degenerates for even $n$, so a lower bound on the representation count reduces to controlling the analytic error term.
-- source:
--   Standard; elementary property of the Goldbach singular series

import Mathlib

namespace WeakGoldbach

theorem singular_series_factor_ge_one (n : ℕ) :
    1 ≤ ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  sorry

end WeakGoldbach
