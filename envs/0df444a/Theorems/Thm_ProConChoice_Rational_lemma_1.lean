-- Prove2me | Theorems.Thm_ProConChoice_Rational_lemma_1
-- name    : ProConChoice.Rational.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:36.453251+00:00
-- url     : https://prove2.me/theorems/aeb33467-69b5-4558-9890-099e1f18dd50
-- title:
--   Lemma 1, p. 14 — if 0 ≤ rᵢ ≤ 1, 0 ≤ cⱼ ≤ m and Σrᵢ = Σcⱼ, a [0,1] matrix with row sums R and column sums C exists
-- statement:
--   Let $R = (r_1, \dots, r_m)$ and $C = (c_1, \dots, c_n)$ be real vectors with $0 \le r_i \le 1$ for every $i$, $0 \le c_j \le m$ for every $j$, and
--   $$\sum_{i=1}^m r_i = \sum_{j=1}^n c_j .$$
--   Then there is an $m \times n$ real matrix $A = (a_{ij})$ with row sum vector $R$, column sum vector $C$, and every entry $a_{ij} \in [0, 1]$.
--
--   Lemma 1 is the building block of the generalized Ford–Fulkerson theorem (Theorem 3), whose proof applies it separately to the nonnegative and to the negated negative parts of the data.
--
--   **Formalization Note** The paper's "positive real-valued vectors" are read as nonnegative, as the hypotheses $0 \le r_i$, $0 \le c_j$ say, and its $\sum c_i$ as $\sum_j c_j$.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 14, Lemma 1

import Mathlib

namespace ProConChoice.Rational

/-- Lemma 1 (p. 14): if `0 ≤ rᵢ ≤ 1`, `0 ≤ cⱼ ≤ m` and `∑ rᵢ = ∑ cⱼ`, there is an `m × n` matrix
with row sums `R`, column sums `C` and every entry in `[0, 1]`. -/
theorem lemma_1 (m n : ℕ) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ m)
    (hsum : ∑ i, r i = ∑ j, c j) :
    ∃ A : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, ∑ j, A i j = r i) ∧ (∀ j, ∑ i, A i j = c j) ∧ (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) := by sorry

end ProConChoice.Rational
