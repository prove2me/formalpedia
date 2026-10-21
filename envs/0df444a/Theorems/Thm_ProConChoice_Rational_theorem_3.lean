-- Prove2me | Theorems.Thm_ProConChoice_Rational_theorem_3
-- name    : ProConChoice.Rational.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:35.389366+00:00
-- url     : https://prove2.me/theorems/d3127657-192f-428a-97eb-e8345b74bbc1
-- title:
--   Theorem 3 (Generalized Ford–Fulkerson), p. 11 — a [−1,1] matrix with real row sums R, column sums C and column bound (iii) exists when 2m ≥ Σ|rᵢ| + Σ|cⱼ|
-- statement:
--   Let $m \ge 0$ and $n \ge 1$, and let $R = (r_1, \dots, r_m)$ and $C = (c_1, \dots, c_n)$ be real vectors with $-1 \le r_i \le 1$, $-m \le c_j \le m$ and $\sum_{i=1}^m r_i = \sum_{j=1}^n c_j$. If
--   $$2m \ \ge\ \sum_{i=1}^m |r_i| + \sum_{j=1}^n |c_j|,$$
--   then there is an $m \times n$ real matrix $A = (a_{ij})$ such that
--
--   1. $A$ has row sum vector $R$ and column sum vector $C$;
--   2. every entry $a_{ij} \in [-1, 1]$;
--   3. for every column $j$,
--   $$\sum_{i=1}^m |a_{ij}| \ \le\ |c_j| + \max\Big\{0,\ \frac{\sum_{i=1}^m |r_i| - \sum_{j'=1}^n |c_{j'}|}{n}\Big\}.$$
--
--   The theorem extends the Ford–Fulkerson criterion to signed data. In the proof of Theorems 1 and 2, the rows are the weights $\lambda_k$ of one step and the columns are Möbius transforms; item 3 is the "forward-looking" bound that keeps the next step's data within the theorem's hypothesis.
--
--   **Formalization Note** The hypothesis $n \ge 1$ is implicit in the page ($C = [c_1, \dots, c_n]$ and the division by $n$); without it the statement is false ($n = 0$, $m = 2$, $R = (1, -1)$). Indices are `Fin m`, `Fin n`, and the division in item 3 is real division by $n > 0$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 11, Theorem 3 (proof in Section 5, pp. 14–16)

import Mathlib

namespace ProConChoice.Rational

/-- Theorem 3 (Generalized Ford–Fulkerson, p. 11): for real `R ∈ [-1, 1]^m`, `C ∈ [-m, m]^n`
(`n ≥ 1`) with equal sums and `2m ≥ ∑ |rᵢ| + ∑ |cⱼ|`, there is an `m × n` matrix with row sums
`R`, column sums `C`, entries in `[-1, 1]`, and column absolute sums
`∑ᵢ |aᵢⱼ| ≤ |cⱼ| + max{0, (∑ |rᵢ| - ∑ |cⱼ|)/n}`. -/
theorem theorem_3 (m n : ℕ) (hn : 0 < n) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (hr : ∀ i, -1 ≤ r i ∧ r i ≤ 1) (hc : ∀ j, -(m : ℝ) ≤ c j ∧ c j ≤ m)
    (hsum : ∑ i, r i = ∑ j, c j)
    (hbound : ∑ i, |r i| + ∑ j, |c j| ≤ 2 * (m : ℝ)) :
    ∃ A : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, ∑ j, A i j = r i) ∧ (∀ j, ∑ i, A i j = c j) ∧
      (∀ i j, -1 ≤ A i j ∧ A i j ≤ 1) ∧
      (∀ j, ∑ i, |A i j| ≤ |c j| + max 0 ((∑ i, |r i| - ∑ j', |c j'|) / n)) := by sorry

end ProConChoice.Rational
