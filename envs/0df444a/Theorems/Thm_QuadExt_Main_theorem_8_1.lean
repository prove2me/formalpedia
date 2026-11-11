-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_8_1
-- name    : QuadExt.Main.theorem_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:04:48.38111+00:00
-- url     : https://prove2.me/theorems/902c5d45-a2df-4daa-8e12-ef690282bfae
-- title:
--   Theorem 8.1 — explicit RCombExt: an $(\varepsilon, 2^{(m-r)/2})$ extractor for derivative-entropy-$d$ quadratic sources and $(\varepsilon, 0)$ for affine sources, $N = \mathrm{poly}(n)$
-- statement:
--   For any $d \ge \log^{40} n$, $\varepsilon \ge 1/n^2$ and $m \le d^{1/10}$ there is an explicit function $\mathrm{RCombExt} : \mathbb F_2^n \times [N] \to \mathbb F_2^m$ with $N = \mathrm{poly}(n)$ such that
--
--   1. $\mathrm{RCombExt}$ is an $(\varepsilon, 2^{(m-r)/2})$-strong linear seeded extractor, with $r \ge d^{1/10}/\log^{3/2} n$, for the class of quadratic sources $X = f(U_k)$ satisfying $H_\infty(\partial_a f(\cdot)) \ge d$ for all non-zero $a$;
--   2. $\mathrm{RCombExt}$ is an $(\varepsilon, 0)$-strong linear seeded extractor for affine sources with entropy at least $d$.
--
--   Explicit means that one polynomial-time machine computes
--   $$\mathrm{RCombExt}(x, i) = F\big(x, 1^d, 1^m, 1^{\lceil 1/\varepsilon\rceil}, 1^i\big),$$
--   the same machine and the same constant $C$ in $N \le C (n+1)^C$ for all $n, d, m, \varepsilon$; logarithms are base 2. $\mathrm{RCombExt}$ provides the seeds $w_i$ of the final extractor (Algorithm 2).
--
--   Differences from the source:
--   - reading: "explicit" → one machine (`LowErrExt.IsPolyTime`) computing $\mathrm{RCombExt}(x, i)$ from $(x, 1^d, 1^m, 1^{\lceil 1/\varepsilon\rceil}, 1^i)$ with output of length exactly $m$; reason: Definition 1.1's polynomial-time algorithm, uniform in all parameters.
--   - encoding: "with $r \ge d^{1/10}/\log^{3/2} n$" → closeness error $2^{(m - d^{1/10}/\log^{3/2} n)/2}$; reason: equivalent, since $2^{(m-r)/2}$ decreases in $r$.
--   - encoding: $N = \mathrm{poly}(n)$ → $1 \le N \le C (n+1)^C$ with $C$ universal; seeds $[N]$ → `Fin N`; reason: explicit form of $\mathrm{poly}(n)$ (the same class as $C n^C$ for $n \ge 1$; $n + 1$ keeps $N \ge 1$ possible at $n = 0$); $N \ge 1$ is part of the seeded-extractor definition.
--   - reading: quadratic sources $X = f(U_k)$ with $H_\infty(\partial_a f) \ge d$ for all non-zero $a$ → $k \ge 1$ (`QuadDerivClass`); reason: at $k = 0$ the derivative condition is vacuous and a constant source would enter the class, which no extractor handles; the paper's class is about sources with non-zero directions $a$.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), pp. 24–25 (PDF 25–26), Theorem 8.1

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_QuadExt_Main_SeededExt
import Definitions.Def_QuadExt_Main_Bits

namespace QuadExt.Main

/-- **Theorem 8.1** (p. 24): one polynomial-time machine `F` and a universal `C` such that for all
`n`, all `d ≥ log₂⁴⁰ n`, `ε ≥ 1/n²` and `m ≤ d^{1/10}` there is `N ≤ C·(n+1)^C` for which
`RCombExt(x, i) = F(x, 1^d, 1^m, 1^{⌈1/ε⌉}, 1^i)` (`i ∈ [N]`, output of length `m`) is (1) an
`(ε, 2^{(m−r)/2})`-strong linear seeded extractor with `r = d^{1/10}/log₂^{3/2} n` for the
quadratic sources `f(U_k)` with `H_∞(∂_a f) ≥ d` for all `a ≠ 0`, and (2) an `(ε, 0)`-strong linear
seeded extractor for affine sources with entropy at least `d`. -/
theorem theorem_8_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ F : List (List Bool) → List Bool, LowErrExt.IsPolyTime F ∧
    ∀ (n d m : ℕ) (ε : ℝ), (Real.logb 2 n) ^ (40 : ℝ) ≤ (d : ℝ) → 1 / (n : ℝ) ^ 2 ≤ ε →
      (m : ℝ) ≤ (d : ℝ) ^ (1 / 10 : ℝ) →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) + 1) ^ C ∧
        (∀ (x : Fin n → ZMod 2) (i : Fin N),
          (F [toBits x, unary d, unary m, unary ⌈1 / ε⌉₊, unary i]).length = m) ∧
        IsSLSEFor (QuadDerivClass n d) ε
            ((2 : ℝ) ^ (((m : ℝ) - (d : ℝ) ^ (1 / 10 : ℝ) / (Real.logb 2 n) ^ (3 / 2 : ℝ)) / 2))
            (fun x (i : Fin N) => ofBits m (F [toBits x, unary d, unary m, unary ⌈1 / ε⌉₊, unary i])) ∧
        IsSLSEFor (AffineClass n d) ε 0
            (fun x (i : Fin N) => ofBits m (F [toBits x, unary d, unary m, unary ⌈1 / ε⌉₊, unary i])) := by sorry

end QuadExt.Main
