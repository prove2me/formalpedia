-- Prove2me | Theorems.Thm_RegretBandits_Contextual_banditron_expected_mistakes
-- name    : RegretBandits.Contextual.banditron_expected_mistakes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:28:49.773421+00:00
-- url     : https://prove2.me/theorems/acfb5301-9fca-4a95-8513-03a766acd4cb
-- title:
--   Theorem 4.7 — expected mistakes of the Banditron
-- statement:
--   Let $K \ge 2$ labels, $n \ge 8K$, and let $(x_1, y_1), \dots, (x_n, y_n) \in \mathbb R^d \times \{1,\dots,K\}$ be any fixed sequence of examples with $\|x_t\| = 1$. Run the Banditron with parameter $\gamma = (K/n)^{1/3}$ and any argmax tie-breaking rule, and let $M_n = \sum_{t=1}^n \mathbb 1_{Y_t \ne y_t}$ be its number of prediction mistakes. Then for every $K\times d$ matrix $U$,
--   $$\mathbb E\,M_n \le L_n(U) + \Big(1 + \|U\|\sqrt{2\bar L_n(U)}\Big) K^{1/3} n^{2/3} + 2\|U\|^2 K^{2/3} n^{1/3} + \sqrt 2\,\|U\|\,K^{1/6} n^{1/3},$$
--   where $\|U\|$ is the Frobenius norm, $L_n(U)$ the cumulative multiclass hinge loss of $U$ and $\bar L_n(U) = L_n(U)/n$ its average. The expectation is over the Banditron's own random predictions.
--
--   With only one bit of feedback per round, the Banditron's multiclass regret against any linear classifier is $O(n^{2/3})$, against $O(\sqrt n)$ for the full-information Perceptron.
--
--   **Formalization Note** Corrected misprint: the book prints the examples as elements of $\mathbb R^d \times \{-1,+1\}$; the algorithm, the hinge loss and the Perceptron display on p. 57 all use labels in $\{1,\dots,K\}$, which the Lean statement uses. The Banditron box asks for $\gamma \in (0, 1/2)$; at $n = 8K$ the prescribed $\gamma$ equals $1/2$, and the proof only uses $\gamma \le 1/2$, so the case $n = 8K$ is included. The infimum over $U$ is written as "for every $U$". $K \ge 2$ is the standing assumption of Section 4.4 (p. 56).
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 59, Theorem 4.7; Banditron p. 58; proof p. 59-62

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol
import Definitions.Def_RegretBandits_Contextual_Multiclass
import Definitions.Def_RegretBandits_Contextual_Banditron

namespace RegretBandits.Contextual

/-- Theorem 4.7 (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 59; labels corrected from the
misprinted `{-1, +1}` to `{1, …, K}`): the Banditron with `γ = (K/n)^{1/3}`, any argmax
tie-breaking rule, run on any fixed sequence of `n ≥ 8K` examples `(x_t, y_t) ∈ ℝ^d × {1, …, K}`
with `‖x_t‖ = 1`, `K ≥ 2`, makes in expectation, for every `K × d` matrix `U`,
`E M_n ≤ L_n(U) + (1 + ‖U‖ √(2 L̄_n(U))) K^{1/3} n^{2/3} + 2‖U‖² K^{2/3} n^{1/3}
  + √2 ‖U‖ K^{1/6} n^{1/3}` prediction mistakes. -/
theorem banditron_expected_mistakes {K d : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 8 * K ≤ n)
    (sel : (Fin K → ℝ) → Fin K) (hsel : IsArgmaxSelector sel)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (hx : ∀ t < n, sqNorm (x t) = 1)
    (U : Matrix (Fin K) (Fin d) ℝ) :
    pathExpect (banditronRule (((K : ℝ) / n) ^ ((1 : ℝ) / 3)) sel x y) n
        (predictionMistakes y) ≤
      cumHinge n x y U
        + (1 + frobNorm U * Real.sqrt (2 * avgHinge n x y U)) *
            (K : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)
        + 2 * frobNorm U ^ 2 * (K : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3)
        + Real.sqrt 2 * frobNorm U * (K : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 3) := by sorry

end RegretBandits.Contextual
