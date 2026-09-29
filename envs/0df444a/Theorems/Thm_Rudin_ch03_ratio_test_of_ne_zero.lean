-- Prove2me | Theorems.Thm_Rudin_ch03_ratio_test_of_ne_zero
-- name    : Rudin.ch03_ratio_test_of_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:14:01.944929+00:00
-- url     : https://prove2.me/theorems/ea6bfe60-b275-48e3-9f9e-6849a00aefef
-- title:
--   Ratio test (Rudin 3.34), corrected
-- statement:
--   **Ratio test.** Let $(a_n)$ be a sequence of complex numbers.
--
--   1. *(Convergence.)* If $a_n \neq 0$ for every $n$ and $\limsup_{n\to\infty} \dfrac{\|a_{n+1}\|}{\|a_n\|} < 1$, then the series $\sum a_n$ converges, i.e. its partial sums converge.
--   2. *(Divergence.)* If there is an $N$ such that $a_n \neq 0$ and $\|a_{n+1}\| \ge \|a_n\|$ for all $n \ge N$, then $\sum a_n$ does not converge.
--
--   This is Rudin's Theorem 3.34, stated with the nonvanishing hypothesis that the book carries implicitly by writing the quotient $a_{n+1}/a_n$.
--
--   **Why the hypothesis is needed in a formal statement.** Lean's division is total, with $x/0 = 0$. Without $a_n \neq 0$, the convergence half is false: take $a_n = 1$ for odd $n$ and $a_n = 0$ for even $n$. Every quotient $\|a_{n+1}\|/\|a_n\|$ is then $0$ (either the numerator vanishes, or the denominator does and the convention makes the quotient $0$), so the $\limsup$ is $0 < 1$, while the partial sums grow without bound. The divergence half already carries $a_n \neq 0$ and is unaffected.
--
--   The ratio here is $\|a_{n+1}\|/\|a_n\|$ rather than $\|a_{n+1}/a_n\|$; the two agree whenever $a_n \neq 0$, which is exactly the regime the corrected statement covers.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 3, Theorem 3.34, p. 66. Corrected form of the platform theorem Rudin.ch03_ratio_test (disproved).

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.34 (ratio test), with the nonvanishing hypothesis Rudin states.
`∑ aₙ` converges if all `aₙ ≠ 0` and `limsup ‖aₙ₊₁ / aₙ‖ < 1`, and diverges if there is an
`N` with `aₙ ≠ 0` and `‖aₙ₊₁‖ ≥ ‖aₙ‖` for all `n ≥ N`. -/
theorem ch03_ratio_test_of_ne_zero (a : ℕ → ℂ) :
    ((∀ n, a n ≠ 0) →
        limsup (fun n => ((‖a (n + 1)‖ / ‖a n‖ : ℝ) : EReal)) atTop < 1 → SeriesConverges a) ∧
    ((∃ N, ∀ n ≥ N, a n ≠ 0 ∧ ‖a n‖ ≤ ‖a (n + 1)‖) → ¬ SeriesConverges a) := by sorry

end Rudin
