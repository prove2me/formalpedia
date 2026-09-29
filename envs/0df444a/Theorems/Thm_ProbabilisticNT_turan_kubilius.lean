-- Prove2me | Theorems.Thm_ProbabilisticNT_turan_kubilius
-- name    : ProbabilisticNT.turan_kubilius
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T03:12:14.638917+00:00
-- url     : https://prove2.me/theorems/9bb00513-ead0-4d14-802c-b58915ce3eab
-- title:
--   The Turan-Kubilius inequality for the number of distinct prime factors
-- statement:
--   The **Turán–Kubilius inequality** measures how tightly the number of distinct prime factors of an
--   integer clusters around its average.
--
--   $$\sum_{n \le x} \bigl(\omega(n) - \log\log x\bigr)^2 \;\le\; C\, x \log\log x$$
--
--   Here $\omega(n)$ is the number of distinct prime factors of $n$, and the sum runs over the integers
--   $1 \le n \le x$. Hardy and Ramanujan showed that $\omega(n)$ has normal order $\log\log n$; this
--   inequality is the quantitative form of that statement, bounding the total squared deviation from
--   $\log\log x$ by $O(x \log\log x)$. Dividing by $x$, the mean square deviation is $O(\log\log x)$,
--   so a typical integer has $\omega(n) = \log\log n + O(\sqrt{\log\log n})$.
--
--   The inequality is the analytic engine behind the Erdős–Kac theorem, which upgrades it to a central
--   limit theorem for $\omega(n)$, and it is the standard tool in probabilistic number theory for
--   controlling additive arithmetic functions by a second-moment argument. Turán's original proof of
--   the Hardy–Ramanujan result rests on exactly this estimate, and it in turn rests on Mertens' second
--   theorem for the sum of reciprocals of primes.
--
--   **Formalization note.** The bound is stated with explicit constants $C$ and a threshold $x_0$, both
--   existentially quantified. The count $\omega(n)$ is `n.primeFactors.card` and the range is
--   `Finset.Icc 1 ⌊x⌋₊`. Only Mathlib is required; no auxiliary definitions are introduced.
-- source:
--   Turan-Kubilius inequality. Lean proof from the Salt project by Jason Hickey, Salt/MR/TuranKubilius.lean with Salt/Mertens/Second.lean (https://github.com/jyh/salt, Apache-2.0).

import Mathlib

namespace ProbabilisticNT

/-- The Turán–Kubilius inequality: the number of distinct prime factors `ω(n)` has
mean square deviation from `log log x` of order `x · log log x`. -/
theorem turan_kubilius :
    ∃ C : ℝ, ∃ x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.primeFactors.card : ℝ) - Real.log (Real.log x)) ^ 2
        ≤ C * x * Real.log (Real.log x) := by
  sorry

end ProbabilisticNT
