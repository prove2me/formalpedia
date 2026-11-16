-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_theorem_4_11
-- name    : ShiAuthentication.BA.Supplement.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:24:09.900742+00:00
-- url     : https://prove2.me/theorems/7319cfa1-813f-49bf-86c5-bca3571196a0
-- title:
--   Theorem 4.11 — authentication complexity of Byzantine agreement
-- statement:
--   For a knowledge setting (public authentication graph, or local key tables only), let $A_{BA}(n,t)$ be the minimum number of authentication edges of a graph on $n$ parties on which Byzantine agreement with fault bound $t$ is possible, and $A^{\max}_{BA}(n,t)$ the minimum over the same graphs of the maximum number $\max_v|K_v|$ of keys initially authenticated to one party; both are $+\infty$ if no such graph exists.
--
--   1. There are absolute constants $c,C>0$ such that for all $n,t$ with $2t<n\le 3t$, with $r=n-2t$, and in both settings,
--   $$A_{BA}(n,t)=\Theta\Big(\min\Big\{n^2,\ \frac{n^2}{r}\ln\frac{en}{r}\Big\}\Big),\qquad A^{\max}_{BA}(n,t)=\Theta\Big(\min\Big\{n,\ \frac{n}{r}\ln\frac{en}{r}\Big\}\Big),$$
--   that is, each quantity lies between $c$ times and $C$ times the displayed function.
--   2. For $n=2t+1$ (with $t\ge1$, so $n\ge 3$), $A_{BA}(n,t)=n(n-1)$ and $A^{\max}_{BA}(n,t)=n-1$.
--   3. For $3\le n\le 2t$ and $t<n$, $A_{BA}(n,t)=A^{\max}_{BA}(n,t)=+\infty$.
--
--   These conclusions hold in either knowledge setting. The theorem determines the optimal setup cost of Byzantine agreement, both in total and per party, as the honest majority margin $r$ varies (Main Theorem 2 in the introduction is its informal version).
--
--   Differences from the source:
--   - encoding: Θ(min{…}) for 2t < n ≤ 3t → ∃ c C > 0 before ∀ mode n t r, with ofReal(c · f) ≤ A ≤ ofReal(C · f); reason: the Θ ranges over the two parameters n, t; constants fixed before them are the uniform reading, and Θ means both bounds
--   - encoding: values of A_T(n, t) in ℕ ∪ {+∞} → ℕ∞, compared with real bounds after the cast ℕ∞ → ℝ≥0∞ and ENNReal.ofReal; reason: +∞ is the infimum of the empty family (Definition 3.3); an upper bound in ℝ≥0∞ also asserts finiteness
--   - encoding: for n ≤ 2t, both are +∞ → 3 ≤ n, t < n, n ≤ 2t → both = ⊤; reason: the model of §3.1 has n ≥ 3 parties and fault bound t < n
--   - encoding: for n = 2t + 1 → n = 2t + 1 with 1 ≤ t; reason: the model of §3.1 has n ≥ 3, i.e. t ≥ 1
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Theorem 4.11, p. 24; informal version Main Theorem 2, p. 3

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

open scoped ENNReal

namespace ShiAuthentication.BA.Supplement

/-- **Theorem 4.11**, p. 24 (informal version: Main Theorem 2, p. 3). In both knowledge settings
(public authentication graph, or local key tables only):
(1) for `2t < n ≤ 3t` and `r = n − 2t`,
`A_BA(n, t) = Θ(min{n², (n²/r) ln(en/r)})` and `A^max_BA(n, t) = Θ(min{n, (n/r) ln(en/r)})`,
with absolute constants `c, C > 0` uniform over all such `n, t` and both settings;
(2) for `n = 2t + 1` (`t ≥ 1`), `A_BA = n(n − 1)` and `A^max_BA = n − 1`;
(3) for `3 ≤ n ≤ 2t`, `t < n`, both are `+∞`.
The finite quantities are compared in `ℝ≥0∞` through the cast `ℕ∞ → ℝ≥0∞`. -/
theorem theorem_4_11 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (mode : Knowledge) (n t r : ℕ), 2 * t < n → n ≤ 3 * t →
      r = n - 2 * t →
      ENNReal.ofReal
          (c * min ((n : ℝ) ^ 2) ((n : ℝ) ^ 2 / r * Real.log (Real.exp 1 * n / r))) ≤
        (ABA mode n t : ℝ≥0∞) ∧
      (ABA mode n t : ℝ≥0∞) ≤
        ENNReal.ofReal
          (C * min ((n : ℝ) ^ 2) ((n : ℝ) ^ 2 / r * Real.log (Real.exp 1 * n / r))) ∧
      ENNReal.ofReal (c * min (n : ℝ) ((n : ℝ) / r * Real.log (Real.exp 1 * n / r))) ≤
        (ABAmax mode n t : ℝ≥0∞) ∧
      (ABAmax mode n t : ℝ≥0∞) ≤
        ENNReal.ofReal (C * min (n : ℝ) ((n : ℝ) / r * Real.log (Real.exp 1 * n / r)))) ∧
    (∀ (mode : Knowledge) (n t : ℕ), 1 ≤ t → n = 2 * t + 1 →
      ABA mode n t = ((n * (n - 1) : ℕ) : ℕ∞) ∧ ABAmax mode n t = ((n - 1 : ℕ) : ℕ∞)) ∧
    (∀ (mode : Knowledge) (n t : ℕ), 3 ≤ n → t < n → n ≤ 2 * t →
      ABA mode n t = ⊤ ∧ ABAmax mode n t = ⊤) := by sorry

end ShiAuthentication.BA.Supplement
