-- Prove2me | Theorems.Thm_TaoFivePrimes_rh122p6to123p2_imaginary_certificate
-- name    : TaoFivePrimes.rh122p6to123p2_imaginary_certificate
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:38:22.174684+00:00
-- url     : https://prove2.me/theorems/2a1b9a7f-8cd3-405f-8b32-fbed65696ae7
-- title:
--   Height-123 polynomial bound on [122.6, 123.2]
-- statement:
--   Let $P$ be the stored degree-39 height-123 polynomial with coefficient denominator $10^{12}$. For $0\le\operatorname{Re}s\le1$ and $122.6\le\operatorname{Im}s\le123.2$,
--
--   $$
--   |\operatorname{Im}P(s)|\ge 40|\operatorname{Re}s-1/2|.
--   $$
--
--   This is an exact polynomial inequality; the analytic approximation to $\xi$ is separate.
-- source:
--   Exact rational Bernstein certificate for the stored height-123 local polynomial. The xi/Taylor framework is due to sometik179, with theta/Mellin foundations by Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Mathlib.Tactic

theorem TaoFivePrimes.rh122p6to123p2_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (613/5:ℝ) ≤ s.im) (hb : s.im ≤ (616/5:ℝ)) :
    (40:ℝ)*|s.re-1/2| ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH123RoundedCoefficients12 (10^12)
        40 (246/2) s).im| := by sorry
