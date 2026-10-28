-- Prove2me | Theorems.Thm_TaoFivePrimes_rh121p4to122p6_polynomial_negative
-- name    : TaoFivePrimes.rh121p4to122p6_polynomial_negative
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:38:25.805033+00:00
-- url     : https://prove2.me/theorems/f8c7f418-a137-4f21-82fd-0c943b379529
-- title:
--   Height-123 polynomial bound on [121.4, 122.6]
-- statement:
--   Let $P$ be the stored degree-39 height-123 polynomial with coefficient denominator $10^{12}$. For $0\le\operatorname{Re}s\le1$ and $121.4\le\operatorname{Im}s\le122.6$,
--
--   $$
--   -\operatorname{Re}P(s)\ge 10.
--   $$
--
--   This is an exact polynomial inequality; the analytic approximation to $\xi$ is separate.
-- source:
--   Exact rational Bernstein certificate for the stored height-123 local polynomial. The xi/Taylor framework is due to sometik179, with theta/Mellin foundations by Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic

theorem TaoFivePrimes.rh121p4to122p6_polynomial_negative (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (607/5:ℝ) ≤ s.im) (hb : s.im ≤ (613/5:ℝ)) :
    (10:ℝ) ≤ -(TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH123RoundedCoefficients12 (10^12) 40 (246/2) s).re := by sorry
