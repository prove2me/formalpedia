-- Prove2me | Theorems.Thm_TaoFivePrimes_abs_theorem51Centered_le
-- name    : TaoFivePrimes.abs_theorem51Centered_le
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:01:44.844801+00:00
-- url     : https://prove2.me/theorems/dfbe7ab0-ba05-4864-82e0-ebdff4ba6c7d
-- title:
--   Tao, after Lemma 4.11: the centred Type II coefficient is at most $\tfrac12\log w$
-- statement:
--   For a parameter $V>0$ and a positive integer $w$, put
--
--   $$g_V(w)\;:=\;\sum_{\substack{b\mid w\\ b>V}}\Lambda(b)\;-\;\frac{\log w}{2},$$
--
--   the von Mangoldt divisor sum of $w$ restricted to divisors exceeding $V$, recentred by half of $\log w$. Then
--
--   $$\bigl|g_V(w)\bigr|\;\le\;\tfrac12\,\log w .$$
--
--   The bound holds for every $V$ and every $w$, and is what makes the recentred coefficient admissible as a Type II coefficient: the divisors of $w$ exceeding $V$ carry a total von Mangoldt weight between $0$ and $\log w$, so subtracting $\tfrac12\log w$ centres it in $[-\tfrac12\log w,\tfrac12\log w]$. Section 5 uses this to feed the bilinear sum into the large sieve with unimodular-up-to-$\tfrac12\log w$ coefficients.
--
--   **Formalization Note** For $w=0$ and $w=1$ both sides vanish, so no positivity hypothesis on $w$ is needed.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, equation (4.19) (the display following Lemma 4.11)

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums

theorem TaoFivePrimes.abs_theorem51Centered_le (V : ℝ) (w : ℕ) :
    |TaoFivePrimes.theorem51Centered V w| ≤ (1/2) * Real.log w := by sorry
