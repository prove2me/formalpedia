-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_8_11
-- name    : QuadExt.Main.theorem_8_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:56.18014+00:00
-- url     : https://prove2.me/theorems/bf10caa6-e10f-4d00-a091-ddfea5e18cff
-- title:
--   Theorem 8.11 — explicit $(d, d^{1/10}/\log^{3/2} n, \varepsilon)$-rank combiner over $\mathbb F_2$, output length $d^{1/10}$, size $\mathrm{poly}(n)$
-- statement:
--   For any $d \ge \log^{40} n$ and $\varepsilon \ge 1/n^2$, there is an explicit $(d, d^{1/10}/\log^{3/2} n, \varepsilon)$-rank combiner over $\mathbb F_2$ with output length $d^{1/10}$ and size $\mathrm{poly}(n)$:
--   $$W_1, \dots, W_N \in \mathbb F_2^{\lceil d^{1/10}\rceil \times n}, \qquad N \le C (n+1)^C .$$
--   Explicit means that one polynomial-time machine, given $1^n$, $1^d$, $1^{\lceil 1/\varepsilon\rceil}$ and $1^i$, outputs the entries of $W_i$ (row by row); the machine and the constant $C$ are the same for all $n, d, \varepsilon$. Logarithms are base 2. Combined with Lemma 8.3 this gives Theorem 8.1.
--
--   Differences from the source:
--   - reading: "explicit" → one machine (`LowErrExt.IsPolyTime`) computing $W_i$ from $(1^n, 1^d, 1^{\lceil 1/\varepsilon\rceil}, 1^i)$; reason: Definition 1.1's "deterministic polynomial time algorithm", uniform in all parameters; all inputs have length polynomial in $n$ ($\lceil 1/\varepsilon\rceil \le n^2$, $i \le N$) apart from $1^d$.
--   - reading: output length $d^{1/10}$ → $\lceil d^{1/10}\rceil$; reason: the output length must be an integer; the ceiling is the stronger reading (deleting rows of a rank combiner keeps it one).
--   - encoding: size $\mathrm{poly}(n)$ → $1 \le N \le C (n+1)^C$ with $C$ universal; reason: explicit form of $\mathrm{poly}(n)$ (the same class as $C n^C$ for $n \ge 1$; $n + 1$ keeps $N \ge 1$ possible at $n = 0$); $N \ge 1$ is part of the rank-combiner definition.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 30 (PDF 31), Theorem 8.11

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_QuadExt_Main_RankCombiner
import Definitions.Def_QuadExt_Main_Bits

namespace QuadExt.Main

/-- **Theorem 8.11** (explicit rank combiner over `𝔽₂`, p. 30): one polynomial-time machine `F`
and a universal `C` such that for all `n`, all `d ≥ log₂⁴⁰ n` and all `ε ≥ 1/n²` there is
`N ≤ C·(n+1)^C` for which `F`, on input `(1^n, 1^d, 1^{⌈1/ε⌉}, 1^i)`, outputs (row by row) a matrix
`W_i ∈ 𝔽₂^{m×n}`, `m = ⌈d^{1/10}⌉`, and `{W_i}_{i∈[N]}` is a
`(d, d^{1/10}/log₂^{3/2} n, ε)`-rank combiner over `𝔽₂` with output length `m` and size `N`. -/
theorem theorem_8_11 :
    ∃ C : ℝ, 0 < C ∧ ∃ F : List (List Bool) → List Bool, LowErrExt.IsPolyTime F ∧
    ∀ (n d : ℕ) (ε : ℝ), (Real.logb 2 n) ^ (40 : ℝ) ≤ (d : ℝ) → 1 / (n : ℝ) ^ 2 ≤ ε →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) + 1) ^ C ∧
        (∀ i : Fin N, (F [unary n, unary d, unary ⌈1 / ε⌉₊, unary i]).length =
          ⌈(d : ℝ) ^ (1 / 10 : ℝ)⌉₊ * n) ∧
        IsRankCombiner d ((d : ℝ) ^ (1 / 10 : ℝ) / (Real.logb 2 n) ^ (3 / 2 : ℝ)) ε
          (fun i : Fin N => Matrix.of fun (j : Fin ⌈(d : ℝ) ^ (1 / 10 : ℝ)⌉₊) (b : Fin n) =>
            ofBits (⌈(d : ℝ) ^ (1 / 10 : ℝ)⌉₊ * n) (F [unary n, unary d, unary ⌈1 / ε⌉₊, unary i])
              (finProdFinEquiv (j, b))) := by sorry

end QuadExt.Main
