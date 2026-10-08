-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_corollary1_i
-- name    : StochIneqPO.Comparison.corollary1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:44.920987+00:00
-- url     : https://prove2.me/theorems/85d85072-96a4-4e90-ba33-905b9e633a36
-- title:
--   Corollary 1 (i) — $P(X_n \in A) \le P(Y_n \in A)$ for increasing $A$
-- statement:
--   Let $E$ be a partially ordered Polish space and $E_1 = E_2 = \cdots = E$. Let $P_1, Q_1$ be probability measures on $E$ with $P_1 \prec Q_1$, and for $n \ge 2$ let $p_n, q_n$ be stochastic kernels from $E^{n-1}$ to $E$ such that
--   $$p_n(x^{n-1}, \cdot) \prec q_n(y^{n-1}, \cdot) \qquad \text{whenever } x^{n-1} \le y^{n-1}. \tag{4}$$
--   Let $(X_n)_{n \ge 1}$ be a random sequence with $X_1 \sim P_1$ and conditional law $p_n(X^{n-1}, \cdot)$ of $X_n$ given $X^{n-1}$, and let $(Y_n)$ be defined likewise from $Q_1$ and $(q_n)$. Then for every increasing measurable set $A \subseteq E$ and every $n$,
--   $$P(X_n \in A) \le P(Y_n \in A).$$
--
--   **Formalization Note** Both sides depend only on the law of the sequence, which is the Ionescu-Tulcea measure `Kernel.trajMeasure P₁ p` on $E^{\mathbb N}$ (resp. `trajMeasure Q₁ q`); the statement is formulated for these laws, which covers "any random sequences" with the given initial and conditional distributions. Indices are 0-based: the paper's $X_n$ is coordinate `n - 1`, and the paper's kernel $p_n$ is `p (n - 2)`. Hypothesis (4) is pointwise for all ordered pairs of histories.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Corollary 1 (i), p. 904 (PDF p. 6), with the paragraph preceding it and Theorem 2, p. 903

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem corollary1_i {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π _ : Iic n, E, x ≤ y → StochLE (p n x) (q n y))
    (A : Set E) (hA : MeasurableSet A) (hAup : IsUpperSet A) (n : ℕ) :
    Kernel.trajMeasure (X := fun _ => E) P₁ p {x | x n ∈ A} ≤
      Kernel.trajMeasure (X := fun _ => E) Q₁ q {x | x n ∈ A} := by sorry

end StochIneqPO.Comparison
