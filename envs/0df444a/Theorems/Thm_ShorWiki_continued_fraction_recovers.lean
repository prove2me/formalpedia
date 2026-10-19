-- Prove2me | Theorems.Thm_ShorWiki_continued_fraction_recovers
-- name    : ShorWiki.continued_fraction_recovers
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:06:48.996011+00:00
-- url     : https://prove2.me/theorems/99d4a73d-eca5-4fee-b98a-8081db4fbd1e
-- title:
--   Continued fractions recover $j/\gcd(j,r)$ and $r/\gcd(j,r)$ from an approximation within $1/(2r^2)$
-- statement:
--   Let $j \ge 0$ and $r \ge 1$ be integers and let $\varphi$ be a real number with
--   $$\left|\frac{j}{r} - \varphi\right| < \frac{1}{2r^2}.$$
--   Then some convergent of the continued fraction expansion of $\varphi$ equals
--   $$\frac{j/\gcd(j,r)}{r/\gcd(j,r)}$$
--   in lowest terms; that is, the continued fractions algorithm run on $\varphi$ recovers both $j/\gcd(j,r)$ and $r/\gcd(j,r)$.
--
--   This is the classical post-processing step that turns the measured approximation of a phase $j/r$ into the reduced fraction itself.
--
--   **Formalization Note** The article states the hypothesis with $\le$; it is formalized with strict $<$. With $\le$ the statement fails for the standard continued fraction expansion used by Mathlib's `Real.convergent`: for $j = r = 1$ and $\varphi = 1/2$ one has $|1 - 1/2| = 1/(2\cdot 1^2)$, but the convergents of $1/2$ are $0$ and $1/2$, never $1$. In the application the inequality is strict (milestone *register size bound* and $r < N$). The article's hypothesis "$j$ and $r$ are $n$-bit integers" places no restriction and is omitted.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Choosing the size of the first register", Theorem (PDF p. 6)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem continued_fraction_recovers (j r : ℕ) (hr : 0 < r) (φ : ℝ)
    (h : |(j : ℝ) / r - φ| < 1 / (2 * (r : ℝ) ^ 2)) :
    ∃ m : ℕ, (Real.convergent φ m).num = ((j / Nat.gcd j r : ℕ) : ℤ) ∧
      (Real.convergent φ m).den = r / Nat.gcd j r := by sorry

end ShorWiki
