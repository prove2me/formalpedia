-- Prove2me | Theorems.Thm_ReadTwiceCount_accuracy_combination
-- name    : ReadTwiceCount.accuracy_combination
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:54.488978+00:00
-- url     : https://prove2.me/theorems/42588b40-7291-4b94-b32e-e5e4eface296
-- title:
--   §8 (43)–(45) — $a_0(j+1)\le\bar\varepsilon/(8n)$ and $1\ge\widehat Z/Z(F)\ge(1-\bar\varepsilon/(8n))^n\ge1-\bar\varepsilon/8\ge1-\varepsilon$
-- statement:
--   Let $n\ge1$, $M\ge0$, $0<\varepsilon\le1$ and $\varepsilon/2<\bar\varepsilon\le\varepsilon$, and let $a_0=\bar\varepsilon/(8(n+1)^2)$ (42). Let $y_j\ge1$ and $U_j$ satisfy $0\le U_j-y_j\le a_0(j+1)$ for $j=1,\dots,n$ (the bound Theorem 6.2 gives for the call on the $j$-clause state $H_j$), and put
--   $$Z(F)=2^M\prod_{j=1}^n\frac1{y_j},\qquad \widehat Z=2^M\prod_{j=1}^n\frac1{U_j}.$$
--   Then for every $j$,
--   $$a_0(j+1)\le\frac{\bar\varepsilon}{8(n+1)}\le\frac{\bar\varepsilon}{8n}\quad(43),\qquad 1\ge\frac{y_j}{U_j}=1-\frac{U_j-y_j}{U_j}\ge1-\frac{\bar\varepsilon}{8n},$$
--   and
--   $$1\ge\frac{\widehat Z}{Z(F)}\ge\Big(1-\frac{\bar\varepsilon}{8n}\Big)^n\ge1-\frac{\bar\varepsilon}8\ge1-\varepsilon .$$
--
--   This is the final accuracy step of Theorem 1.1: the returned rational $\widehat Z$ is within a factor $1-\varepsilon$ of the count.
--
--   Differences from the source:
--   - reading: $Z(F)$ in (45) → its telescoped form $2^M\prod_j 1/y_j$ from (41); reason: (41), stated in `private_literal`, identifies the two; the display uses only this form
--   - reading: "Theorem 6.2 gives $0\le U_j-y_j\le a_0(j+1)$" in (43) → the hypothesis $0\le U_j-y_j\le a_0(j+1)$, the rest of the chain (43) in the conclusion; reason: that step is Theorem 6.2 (item `theorem_6_2`) applied to the $j$-clause state $H_j$ with density $a_0$; the remaining inequalities of (43) are stated
--   - generalization: $\bar\varepsilon$ dyadic and $y_j,U_j$ rational → $\bar\varepsilon$, $y_j$, $U_j$ any reals with the stated bounds; reason: the paper's values satisfy the bounds, and the inequalities use nothing else
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §8, displays (42)–(45), p.14

import Mathlib

namespace ReadTwiceCount

/-- **Combining the marginal bounds (43)–(45)** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §8,
displays (42)–(45), p.14): with the initial density `a₀ = ε̄/(8(n + 1)²)` (42), `yⱼ ≥ 1` and the
bound `0 ≤ Uⱼ − yⱼ ≤ a₀(j + 1)` that Theorem 6.2 gives on the `j`-clause state `Hⱼ`, for
`j = 1, …, n`: "a₀(j + 1) ≤ ε̄/(8(n + 1)) ≤ ε̄/(8n)" (43),
"1 ≥ yⱼ/Uⱼ = 1 − (Uⱼ − yⱼ)/Uⱼ ≥ 1 − ε̄/(8n)", and for `Ẑ = 2^M ∏ⱼ 1/Uⱼ` (44) and
`Z(F) = 2^M ∏ⱼ 1/yⱼ` (41),
"1 ≥ Ẑ/Z(F) ≥ (1 − ε̄/(8n))^n ≥ 1 − ε̄/8 ≥ 1 − ε" (45), where `0 < ε ≤ 1` and `ε/2 < ε̄ ≤ ε`.

**Formalization Note** `Z(F)` is written as its telescoped form `2^M ∏ⱼ 1/yⱼ` (41), which
`private_literal` identifies with the count. `ε̄` is any real with `ε/2 < ε̄ ≤ ε` (the paper picks a
dyadic one, §7.2). The hypothesis on `Uⱼ − yⱼ` is the output of Theorem 6.2 (`theorem_6_2`) for the
call `Solve(Hⱼ, hⱼ, a₀)`, whose state has `j` clauses. -/
theorem accuracy_combination (n M : ℕ) (hn : 1 ≤ n) (ε εb : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεb : ε / 2 < εb ∧ εb ≤ ε) (a₀ : ℝ) (ha₀ : a₀ = εb / (8 * ((n : ℝ) + 1) ^ 2))
    (y U : ℕ → ℝ) (hy : ∀ j ∈ Finset.Icc 1 n, 1 ≤ y j)
    (hU : ∀ j ∈ Finset.Icc 1 n, 0 ≤ U j - y j ∧ U j - y j ≤ a₀ * ((j : ℝ) + 1)) :
    let Zr : ℝ := 2 ^ M * ∏ j ∈ Finset.Icc 1 n, 1 / y j
    let Zhat : ℝ := 2 ^ M * ∏ j ∈ Finset.Icc 1 n, 1 / U j
    (∀ j ∈ Finset.Icc 1 n, a₀ * ((j : ℝ) + 1) ≤ εb / (8 * ((n : ℝ) + 1)) ∧
        εb / (8 * ((n : ℝ) + 1)) ≤ εb / (8 * n)) ∧
      (∀ j ∈ Finset.Icc 1 n, y j / U j ≤ 1 ∧ y j / U j = 1 - (U j - y j) / U j ∧
        1 - εb / (8 * n) ≤ 1 - (U j - y j) / U j) ∧
      Zhat / Zr ≤ 1 ∧ (1 - εb / (8 * n)) ^ n ≤ Zhat / Zr ∧
      1 - εb / 8 ≤ (1 - εb / (8 * n)) ^ n ∧ 1 - ε ≤ 1 - εb / 8 := by sorry

end ReadTwiceCount
