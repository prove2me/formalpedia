-- Prove2me | Theorems.Thm_TaoFivePrimes_rh123p2to124_polynomial_positive
-- name    : TaoFivePrimes.rh123p2to124_polynomial_positive
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:38:28.222998+00:00
-- url     : https://prove2.me/theorems/c1cefd0b-defb-48c4-a147-a96690eb9933
-- title:
--   Height-123 polynomial bound on [123.2, 124]
-- statement:
--   Let $P$ be the stored degree-39 height-123 polynomial with coefficient denominator $10^{12}$. For $0\le\operatorname{Re}s\le1$ and $123.2\le\operatorname{Im}s\le124$,
--
--   $$
--   \operatorname{Re}P(s)\ge 10.
--   $$
--
--   This is an exact polynomial inequality; the analytic approximation to $\xi$ is separate.
-- source:
--   Exact rational Bernstein certificate for the stored height-123 local polynomial. The xi/Taylor framework is due to sometik179, with theta/Mellin foundations by Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic

theorem TaoFivePrimes.rh123p2to124_polynomial_positive (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (616/5:ℝ) ≤ s.im) (hb : s.im ≤ (124:ℝ)) :
    (10:ℝ) ≤ (TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH123RoundedCoefficients12 (10^12) 40 (246/2) s).re := by sorry
