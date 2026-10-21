-- Prove2me | Theorems.Thm_ProConChoice_Rational_theorem_4
-- name    : ProConChoice.Rational.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:37.741864+00:00
-- url     : https://prove2.me/theorems/86e2e8c8-2706-47e6-bd85-11797ae43eb0
-- title:
--   Theorem 4 (Ford–Fulkerson), p. 14 — a [0,1] matrix with nonnegative row sums R and column sums C exists iff |I||J| ≥ Σ_{i∈I} rᵢ − Σ_{j∉J} cⱼ
-- statement:
--   Let $R = (r_1, \dots, r_m)$ and $C = (c_1, \dots, c_n)$ be vectors of nonnegative reals with $\sum_{i=1}^m r_i = \sum_{j=1}^n c_j$. There is an $m \times n$ real matrix $A = (a_{ij})$ with row sums $R$, column sums $C$ and every entry $a_{ij} \in [0, 1]$ if and only if, for all $I \subseteq \{1, \dots, m\}$ and $J \subseteq \{1, \dots, n\}$,
--   $$|I|\,|J| \ \ge\ \sum_{i \in I} r_i - \sum_{j \notin J} c_j. \qquad \text{(FF)}$$
--
--   This is the Ford–Fulkerson feasibility criterion for bounded transportation problems, which the paper cites and uses to prove Lemma 1.
--
--   **Formalization Note** The paper says "positive real-valued vectors"; its use (Lemma 1, which assumes $0 \le r_i$, $0 \le c_j$) is for nonnegative vectors, which is how it is stated here. Indices are `Fin m`, `Fin n`; $I$ and $J$ range over all subsets, including the empty ones.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 14, Theorem 4 (Ford Jr & Fulkerson), condition (FF)

import Mathlib

namespace ProConChoice.Rational

/-- Theorem 4 (Ford–Fulkerson, p. 14): for nonnegative real vectors `R ∈ ℝ^m`, `C ∈ ℝ^n` with
equal sums, an `m × n` matrix with row sums `R`, column sums `C` and entries in `[0, 1]` exists
iff `|I| |J| ≥ ∑_{i ∈ I} rᵢ - ∑_{j ∉ J} cⱼ` for all `I ⊆ {1, …, m}`, `J ⊆ {1, …, n}`. -/
theorem theorem_4 (m n : ℕ) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ i, r i = ∑ j, c j) :
    (∃ A : Matrix (Fin m) (Fin n) ℝ,
        (∀ i, ∑ j, A i j = r i) ∧ (∀ j, ∑ i, A i j = c j) ∧ (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)) ↔
    (∀ I : Finset (Fin m), ∀ J : Finset (Fin n),
        ∑ i ∈ I, r i - ∑ j ∈ Jᶜ, c j ≤ (I.card : ℝ) * J.card) := by sorry

end ProConChoice.Rational
