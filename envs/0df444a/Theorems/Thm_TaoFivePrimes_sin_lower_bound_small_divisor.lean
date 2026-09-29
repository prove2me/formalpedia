-- Prove2me | Theorems.Thm_TaoFivePrimes_sin_lower_bound_small_divisor
-- name    : TaoFivePrimes.sin_lower_bound_small_divisor
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:19:09.495104+00:00
-- url     : https://prove2.me/theorems/b0a89876-0f05-45eb-8551-40e3fe8c0689
-- title:
--   Tao Section 5: the reciprocal-sine weight is at most $2q$ for divisors $d \le q/2$
-- statement:
--   Let $q\ge2$, let $a$ be an integer coprime to $q$, and let $\alpha$ satisfy
--   $$4\alpha=\frac aq+\beta,\qquad |\beta|\le\frac1{q^2}.$$
--   Then for every integer $d$ with $1\le d\le q/2$,
--   $$\|4d\alpha\|_{\mathbb R/\mathbb Z}\ \ge\ \frac1{2q}\qquad\text{and}\qquad |\sin(2\pi d\alpha)|\ \ge\ \frac1{2q},$$
--   where $\|t\|_{\mathbb R/\mathbb Z}$ denotes the distance from $t$ to the nearest integer.
--
--   These are the two displayed bounds that open the estimation of the Type I sum in the source's minor-arc argument: the small divisors $d\le q/2$ cannot make the frequency $4d\alpha$ nearly integral, because $ad$ is then not divisible by $q$ while the perturbation $d\beta$ is at most half the resulting gap. The second bound is what lets the reciprocal-sine weight $1/|\sin(2\pi d\alpha)|$ in the Type I envelope be replaced by the constant $2q$ on that range, before the Vinogradov-type lemma is applied to the remaining blocks.
--
--   **Formalization Note** The distance to the nearest integer is written $|t-\operatorname{round}(t)|$. The hypothesis $d\le q/2$ is stated as $2d\le q$ over the natural numbers, and coprimality of $a$ to $q$ as coprimality of $|a|$ to $q$. The source assumes $q\ge4$ throughout its minor-arc theorem; only $q\ge2$ is needed here.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 5 (Minor arcs), subsection "Estimation of the Type I sum", the two displayed bounds labelled (ala) and (daa) that control the contribution of the terms d <= q/2 to the Type I envelope; the comparison |sin(pi t)| >= 2||t|| used in the second bound is equation (2.1) of Section 2

import Mathlib

theorem TaoFivePrimes.sin_lower_bound_small_divisor
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (d : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 * d ≤ q) :
    1 / (2 * (q : ℝ)) ≤ |4 * (d : ℝ) * alpha - round (4 * (d : ℝ) * alpha)|
      ∧ 1 / (2 * (q : ℝ)) ≤ |Real.sin (2 * Real.pi * (d : ℝ) * alpha)| := by sorry
