-- Prove2me | Theorems.Thm_RegretBandits_Contextual_perceptron_mistake_bound
-- name    : RegretBandits.Contextual.perceptron_mistake_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:10:44.455014+00:00
-- url     : https://prove2.me/theorems/ab726537-b55f-4bcf-83fe-0cd2bf5f0d22
-- title:
--   Multiclass Perceptron mistake bound (Section 4.4, p. 57)
-- statement:
--   Let $K \ge 2$ and let $(x_1, y_1), (x_2, y_2), \dots \in \mathbb R^d \times \{1,\dots,K\}$ be any sequence of examples with $\|x_t\| = 1$ (Euclidean norm). Run the multiclass Perceptron with any argmax tie-breaking rule, and let $\hat y_t$ be its prediction at round $t$. Then for every $n \ge 1$ and every $K\times d$ matrix $U$,
--   $$\sum_{t=1}^n \mathbb 1_{\hat y_t \ne y_t} \;\le\; L_n(U) + 2\|U\|^2 + \|U\|\sqrt{2n\bar L_n(U)},$$
--   where $\|U\|$ is the Frobenius norm, $L_n(U)$ the cumulative multiclass hinge loss and $\bar L_n(U) = L_n(U)/n$.
--
--   The bound compares the mistakes of the Perceptron with the hinge loss of any fixed linear classifier. It is the full-information baseline of the Banditron analysis, and it is the template of that analysis.
--
--   **Formalization Note** The book writes the bound as an infimum over $U$; the Lean statement is the equivalent "for every $U$". "Uniformly over $n \ge 1$" is the quantifier over all $n \ge 1$ for one fixed example sequence. The book states $K \ge 2$ at the start of Section 4.4.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 57, Section 4.4 (unnumbered display)

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Multiclass

namespace RegretBandits.Contextual

/-- Multiclass Perceptron mistake bound (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, Section 4.4,
p. 57): for `K ≥ 2` labels, any argmax tie-breaking rule, any examples `(x_t, y_t)` with
`‖x_t‖ = 1`, every horizon `n ≥ 1` and every `K × d` matrix `U`,
`∑_{t ≤ n} 1{ŷ_t ≠ y_t} ≤ L_n(U) + 2‖U‖² + ‖U‖ √(2 n L̄_n(U))` (Frobenius norm). -/
theorem perceptron_mistake_bound {K d : ℕ} (hK : 2 ≤ K)
    (sel : (Fin K → ℝ) → Fin K) (hsel : IsArgmaxSelector sel)
    (x : ℕ → Fin d → ℝ) (y : ℕ → Fin K) (hx : ∀ t, sqNorm (x t) = 1)
    (n : ℕ) (hn : 1 ≤ n) (U : Matrix (Fin K) (Fin d) ℝ) :
    perceptronMistakes sel x y n ≤
      cumHinge n x y U + 2 * frobNorm U ^ 2 +
        frobNorm U * Real.sqrt (2 * n * avgHinge n x y U) := by sorry

end RegretBandits.Contextual
