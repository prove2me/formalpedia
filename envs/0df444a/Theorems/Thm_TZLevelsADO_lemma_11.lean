-- Prove2me | Theorems.Thm_TZLevelsADO_lemma_11
-- name    : TZLevelsADO.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:48:58.054933+00:00
-- url     : https://prove2.me/theorems/c61386d3-21e7-4955-becc-80a0a45b60ff
-- title:
--   Lemma 11 — the numerical optimization, value at most $\frac35 k + 2$
-- statement:
--   Let $k \ge 1$ be an integer and let $x_1, \dots, x_{k-1}, y_1, \dots, y_{k-1} \ge 0$ with $x_1, y_1 \le 2$ (when $k \ge 2$). For $0 \le i \le k-1$ let $X_i = \sum_{r=1}^{i} x_r$ and $Y_i = \sum_{r=1}^{i} y_r$. Then
--   $$\min\Big\{ X_{k-1},\ Y_{k-1},\ \min_{\substack{2\le i\le k-1\\ X_i > Y_{i-2}+1}} \Big(Y_{i-2} + \frac{X_{i-1}+X_i}{2}\Big),\ \min_{\substack{2\le i\le k-1\\ Y_i > X_{i-2}+1}} \Big(X_{i-2} + \frac{Y_{i-1}+Y_i}{2}\Big),$$
--   $$\min_{\substack{2\le i\le k-1,\ 1\le j\le k-1\\ x_i+x_{i-1}+y_j>2}} (X_{i-1}+Y_{j-1}),\ \min_{\substack{2\le i\le k-1,\ 1\le j\le k-1\\ y_i+y_{i-1}+x_j>2}} (Y_{i-1}+X_{j-1}) \Big\} \le \frac35 k + 2,$$
--   where an inner minimum over an empty index set is $+\infty$.
--
--   With $x_i = \Delta_i(u)/D$ and $y_i = \Delta_i(v)/D$ the terms are the three graph bounds of §5.5 divided by $2D$; the lemma says one of them is small, which yields the stretch $\frac65 k + 7$.
--
--   **Formalization Note** The conclusion is stated as "one of the terms, with its side condition, is at most $\frac35 k + 2$", which is equivalent to the minimum being at most that value since the minimum is attained. The sequences are functions on $\mathbb N$ of which only the indices $1, \dots, k-1$ are constrained or used.
--
--   Differences from the source:
--   - encoding: min{…} ≤ 3/5·k + 2 over six terms, an empty inner minimum being +∞ → a disjunction: some term, with an index satisfying its side condition, is at most 3/5·k + 2; reason: the minimum of finitely many attained terms is ≤ B exactly when one term is ≤ B
--   - encoding: x₁, …, x_{k−1}, y₁, …, y_{k−1} with x₁, y₁ ≤ 2 → functions x, y : ℕ → ℝ, nonnegative on 1, …, k−1, with x 1, y 1 ≤ 2 required when k ≥ 2; reason: only the indices 1, …, k−1 enter; x₁, y₁ exist only when k ≥ 2
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Lemma 11, p.23 (PDF p.24); proof App. A.2, pp.39–41

import Mathlib

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Lemma 11, p.23 (PDF p.24; proof in App. A.2, pp.39–41):
"Let x_1, …, x_{k−1}, y_1, …, y_{k−1} ≥ 0 with x_1, y_1 ≤ 2, and for every 0 ≤ i ≤ k−1 let
X_i = Σ_{r=1}^i x_r and Y_i = Σ_{r=1}^i y_r. Then
min { X_{k−1}, Y_{k−1}, min_{2≤i≤k−1, X_i>Y_{i−2}+1} (Y_{i−2} + (X_{i−1} + X_i)/2),
min_{2≤i≤k−1, Y_i>X_{i−2}+1} (X_{i−2} + (Y_{i−1} + Y_i)/2),
min_{2≤i≤k−1, 1≤j≤k−1, x_i+x_{i−1}+y_j>2} (X_{i−1} + Y_{j−1}),
min_{2≤i≤k−1, 1≤j≤k−1, y_i+y_{i−1}+x_j>2} (Y_{i−1} + X_{j−1}) } ≤ 3/5 k + 2."

**Formalization Note.**
* The sequences are `x y : ℕ → ℝ`; only the indices `1, …, k−1` are constrained or used.
  `X i = Σ_{r ∈ [1, i]} x r`, so `X 0 = 0`. "x_1, y_1 ≤ 2" is required only when `x_1, y_1` exist,
  i.e. `k ≥ 2`.
* The minimum of finitely many terms, each inner minimum being `+∞` when no index satisfies its side
  condition, is at most `B = 3/5·k + 2` exactly when one of the terms is at most `B` (the minimum is
  attained). The conclusion is written as that disjunction.
* `k` is a positive integer (p.1). -/
theorem lemma_11 (k : ℕ) (hk : 1 ≤ k) (x y : ℕ → ℝ)
    (hx : ∀ r, 1 ≤ r → r ≤ k - 1 → 0 ≤ x r) (hy : ∀ r, 1 ≤ r → r ≤ k - 1 → 0 ≤ y r)
    (hx1 : 2 ≤ k → x 1 ≤ 2) (hy1 : 2 ≤ k → y 1 ≤ 2) :
    let X : ℕ → ℝ := fun i => ∑ r ∈ Finset.Icc 1 i, x r
    let Y : ℕ → ℝ := fun i => ∑ r ∈ Finset.Icc 1 i, y r
    let B : ℝ := 3 / 5 * k + 2
    X (k - 1) ≤ B ∨ Y (k - 1) ≤ B ∨
      (∃ i, 2 ≤ i ∧ i ≤ k - 1 ∧ X i > Y (i - 2) + 1 ∧ Y (i - 2) + (X (i - 1) + X i) / 2 ≤ B) ∨
      (∃ i, 2 ≤ i ∧ i ≤ k - 1 ∧ Y i > X (i - 2) + 1 ∧ X (i - 2) + (Y (i - 1) + Y i) / 2 ≤ B) ∨
      (∃ i j, 2 ≤ i ∧ i ≤ k - 1 ∧ 1 ≤ j ∧ j ≤ k - 1 ∧ x i + x (i - 1) + y j > 2 ∧
        X (i - 1) + Y (j - 1) ≤ B) ∨
      (∃ i j, 2 ≤ i ∧ i ≤ k - 1 ∧ 1 ≤ j ∧ j ≤ k - 1 ∧ y i + y (i - 1) + x j > 2 ∧
        Y (i - 1) + X (j - 1) ≤ B) := by sorry

end TZLevelsADO
