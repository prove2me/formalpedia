-- Prove2me | Theorems.Thm_TaoFivePrimes_tao_totient_cert_h_check
-- name    : TaoFivePrimes.tao_totient_cert_h_check
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T20:45:08.658081+00:00
-- url     : https://prove2.me/theorems/26399570-9baa-47a8-8e1b-434ec9508a73
-- title:
--   Certificate inequality for the primorial sample points (m = 4..65)
-- statement:
--   Let $P_m = p_1 p_2 \cdots p_m$ be the product of the first $m$ primes (the primorial), so that $P_m / \varphi(P_m) = \prod_{i=1}^{m} p_i/(p_i-1)$ is the totient ratio at the primorial sample point. The table `Qpt m` holds these ratios; the table `rll m` holds certified rational lower bounds for $\log\log P_m$.
--
--   The theorem certifies, for every $4 \le m \le 65$, the rational inequality
--   $$ R_m \cdot 1.78107237 \;+\; \frac{2.50637}{R_m} \;>\; Q_m, $$
--   where $R_m = \mathrm{rll}(m)$, $Q_m = \mathrm{Qpt}(m)$, and $1.78107237$ is a certified lower bound for $e^{\gamma}$.
--
--   Because $e^{\gamma} \ge 1.78107237$, $\log\log P_m \ge R_m$, and $t \mapsto 1.78107237\,t + 2.50637/t$ is increasing for $t > \sqrt{2.50637/1.78107237} \approx 1.19$ while $R_m \ge 1.67$ throughout the range, this is exactly the pointwise Rosser--Schoenfeld totient bound
--   $$ \frac{n}{\varphi(n)} \;<\; e^{\gamma} \log\log n + \frac{2.50637}{\log\log n} $$
--   evaluated at the 62 sample points $n = P_m$, $4 \le m \le 65$. It is the arithmetic core of the finite verification: the remaining sample points $n \le p_4\cdots p_4$ are handled separately by a monotonicity argument.
-- source:
--   Numerical certificate for the finite part of the Rosser--Schoenfeld tribute: J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Theorem 15 (equation (3.42)); the constants 1.78107237 and 2.50637 are certified in this development (`TaoFivePrimes.theta_cert_totient_gamma_lower` and the exponential certificates of `Def_TaoFivePrimes_theta_cert_tables`).

import Definitions.Def_TaoFivePrimes_totient_cert_tables

namespace TaoFivePrimes

theorem tao_totient_cert_h_check (m : ℕ) (hm : m ∈ Finset.Icc 4 65) :
    (rll m : ℚ) * (178107237 / 10^8) + (250637 / 10^5) / (rll m) > Qpt m := by sorry

end TaoFivePrimes
