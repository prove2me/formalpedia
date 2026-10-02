-- Prove2me | Theorems.Thm_Transcendence_siegel_small_values_parameters
-- name    : Transcendence.siegel_small_values_parameters
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:09.921341+00:00
-- url     : https://prove2.me/theorems/65e8b744-5d79-469e-aee5-891c31c9b115
-- title:
--   The choice of T, X and ℓ in the proof of Proposition 4.10 of Waldschmidt's book
-- statement:
--   Let $n \ge 1$ and $L$ be integers and $N, U, V, r, R$ real numbers with $r > 0$, $W = N + U + V \ge 12n^2$, $e \le R/r \le e^{W/6}$ and
--
--   $$(2W)^{n+1} \le L\,N\,\bigl(\log(R/r)\bigr)^{n}.$$
--
--   Then there are integers $T$, $X$ and $\ell \ge 1$ with $X \le e^{N}$, $\ell^{2T^n} < (X+1)^{L}$,
--
--   $$T^n\cdot\frac{2e^{U}X}{\ell} \le \frac34\,e^{-V} \qquad\text{and}\qquad \frac{Xe^{U}(r/R)^{T}}{1 - r/R} \le \frac14\,e^{-V}.$$
--
--   These are the conditions under which `Transcendence.siegel_small_values_of_count`, with $C = e^U$, gives Proposition 4.10 (`Transcendence.siegel_small_values`).
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the numerical part of the proof of Proposition 4.10 of Waldschmidt's book (pp. 135–136), with the book's $T$, defined by $\frac43W \le T\log(R/r) < \frac43W + \log(R/r)$, the book's $X = \lfloor e^N\rfloor$, and an explicit number of cells $\ell = \lceil\frac83T^ne^W\rceil$ for the box principle. It proves the book's inequality $3(\frac43W + 1)^n < e^{W/3}$ for $W \ge 12n^2$, which is tight at $n = 1$, $W = 12$ ($51 < e^4 \approx 54.6$). The contribution of this node is the formal proof.
-- source:
--   The numerical part of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 4.10 (pp. 135–136). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **The parameters of Prop. 4.10** (Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*,
proof of Prop. 4.10). Let `n ≥ 1` and `L` be integers and `N, U, V, r, R` reals with `r > 0`,
`W = N + U + V ≥ 12n²`, `e ≤ R/r ≤ e^{W/6}` and `(2W)^{n+1} ≤ L·N·(log(R/r))ⁿ`. Then there are integers
`T`, `X` and `ℓ ≥ 1` with `X ≤ e^N`, `ℓ^{2Tⁿ} < (X + 1)^L`, `Tⁿ · 2 e^U X / ℓ ≤ (3/4) e^{-V}` and
`X e^U (r/R)^T / (1 - r/R) ≤ (1/4) e^{-V}`. -/
theorem siegel_small_values_parameters {n L : ℕ} (hn : 0 < n) {N U V r R : ℝ} (hr : 0 < r)
    (hW : 12 * (n : ℝ) ^ 2 ≤ N + U + V)
    (hRe : Real.exp 1 * r ≤ R) (hRW : R ≤ r * Real.exp ((N + U + V) / 6))
    (hmain : (2 * (N + U + V)) ^ (n + 1) ≤ L * N * Real.log (R / r) ^ n) :
    ∃ T X ℓ : ℕ, 0 < ℓ ∧ (X : ℝ) ≤ Real.exp N ∧ ℓ ^ (2 * T ^ n) < (X + 1) ^ L ∧
      (T : ℝ) ^ n * (2 * (Real.exp U * X / ℓ)) ≤ 3 / 4 * Real.exp (-V) ∧
      X * Real.exp U * (r / R) ^ T / (1 - r / R) ≤ 1 / 4 * Real.exp (-V) := by
  sorry

end Transcendence
