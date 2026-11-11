-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_1_3
-- name    : QuadExt.Main.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:04:04.437488+00:00
-- url     : https://prove2.me/theorems/04ed7086-4a54-4871-a76e-64a6c90756be
-- title:
--   Theorem 1.3 — an explicit extractor for quadratic sources over $\mathbb F_2$ with entropy $\log^C n$, error $n^{-\Omega(1)}$ and output length $k^{\Omega(1)}$
-- statement:
--   There are universal constants $C > 0$ and $c > 0$ and one deterministic polynomial-time algorithm $\mathrm{QExt}$ with the following property. For every $n$ and every integer $k \ge (\log_2 n)^C$, on inputs $(x, 1^k)$ with $x \in \{0,1\}^n$ the algorithm outputs a string of one fixed length $m = m(n, k) \ge k^c$, and for every quadratic source $X$ over $\mathbb F_2$ on $n$ bits with $H_\infty(X) \ge k$,
--   $$d_{TV}\big(\mathrm{QExt}(X, 1^k),\ U_m\big) \le n^{-c}.$$
--   Here a quadratic source is $X = f(U_s)$ for any number $s$ of generating bits and any map $f : \mathbb F_2^s \to \mathbb F_2^n$ whose coordinates are polynomials of total degree at most $2$ over $\mathbb F_2$. This is the paper's main result: the previous best entropy requirement for quadratic sources over $\mathbb F_2$ was roughly $n - \sqrt{\log n}$.
--
--   Differences from the source:
--   - reading: "there exists an explicit function $\mathrm{QExt}$" (for each $k$) → one machine `F` with `LowErrExt.IsPolyTime F`, chosen after $C, c$ and before $n, k$, run on $[x, 1^k]$; reason: Definition 1.1's "deterministic polynomial time algorithm"; with $k$ in unary, time polynomial in the input is polynomial in $n$ on the only meaningful range $k \le n$.
--   - encoding: $n^{-\Omega(1)}$ and $m = k^{\Omega(1)}$ → one universal $c > 0$ with error $\le n^{-c}$ and $m \ge k^c$, the output having length exactly $m$ on every $x$ of length $n$; reason: the asymptotic notation made explicit.
--   - encoding: $k$ a natural number; reason: an integer threshold is the same up to the existential constants.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 2 (PDF 3), Theorem 1.3 (restated as Theorem 9.4, p. 32)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Bits

namespace QuadExt.Main

/-- **Theorem 1.3** (p. 2): one polynomial-time machine `F`, on input `(x, 1^k)` with `|x| = n`,
outputs `m(n, k) ≥ k^c` bits that are `n^{−c}`-close to uniform for every quadratic source `X` over
`𝔽₂` with `H_∞(X) ≥ k`, whenever `k ≥ (log₂ n)^C`. -/
theorem theorem_1_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∃ F : List (List Bool) → List Bool, LowErrExt.IsPolyTime F ∧
    ∀ n k : ℕ, (Real.logb 2 n) ^ C ≤ (k : ℝ) →
      ∃ m : ℕ, (k : ℝ) ^ c ≤ (m : ℝ) ∧
        (∀ x : Fin n → ZMod 2, (F [toBits x, unary k]).length = m) ∧
        ∀ (s : ℕ) (f : (Fin s → ZMod 2) → (Fin n → ZMod 2)),
          IsQuadraticMap f → (k : ℝ) ≤ SSNonExt.minEntropy (source f) →
          SSNonExt.TV ((source f).map fun x => ofBits m (F [toBits x, unary k]))
            (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ (n : ℝ) ^ (-c) := by sorry

end QuadExt.Main
