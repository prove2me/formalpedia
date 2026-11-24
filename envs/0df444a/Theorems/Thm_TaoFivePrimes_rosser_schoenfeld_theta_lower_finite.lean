-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T09:28:02.569026+00:00
-- url     : https://prove2.me/theorems/37e2424b-e677-44ff-972d-1490e9e5062f
-- title:
--   Rosser–Schoenfeld (1962), Theorem 19: finite-range lower bound for θ
-- statement:
--   Let $\theta$ be the Chebyshev function, $\theta(t) = \sum_{p \le t} \log p$ over primes $p$. For every real $t$ with $255 \le t \le 1420$,
--   $$t - 2\sqrt{t} \;<\; \theta(t).$$
--
--   This is the finite window of Theorem 19 of Rosser and Schoenfeld (1962), which states $x - 2\sqrt{x} < \theta(x)$ for $0 < x \le 1420.9$ (and again for $1423 \le x \le 10^8$). It is the input used in §9 of that paper (p. 89) to construct the parameter $y$ of Lemma 15 in the range $255 \le \log n \le 1340$: taking $y = 2 + 2\sqrt{1+\log n}$ makes $\log n + y = (\sqrt{1+\log n}+1)^2$, so that $\log n = (\log n + y) - 2\sqrt{\log n + y} < \theta(\log n + y)$. For $\log n \in [294, 1340]$ the argument $t = \log n + y$ lies in $[255, 1420]$, so only this finite window is needed.
--
--   Formalization note: `Chebyshev.theta` is Mathlib's $\theta$ function on $\mathbb{R}$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94, Theorem 19, p. 82, eq. (4.6); used in §9, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_finite (t : ℝ) (h1 : 255 ≤ t) (h2 : t ≤ 1420) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by sorry

end TaoFivePrimes
