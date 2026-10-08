-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_corollary1_ii
-- name    : StochIneqPO.Comparison.corollary1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:49.399266+00:00
-- url     : https://prove2.me/theorems/7b06d1e4-7124-43a4-a64f-1081eab05e63
-- title:
--   Corollary 1 (ii) — first entrance times into an increasing set: $P(N_x < n) \le P(N_y < n)$
-- statement:
--   In the setting of Corollary 1 (i) — $E_1 = E_2 = \cdots = E$ a partially ordered Polish space, $P_1 \prec Q_1$, kernels satisfying (4), and random sequences $(X_n)$, $(Y_n)$ with the corresponding initial and conditional laws — let $A \subseteq E$ be an increasing measurable set and let
--   $$N_x = \min\{n \ge 1 : X_n \in A\} \quad (= \infty \text{ if } X_n \notin A \text{ for all } n),$$
--   and define $N_y$ likewise from $(Y_n)$. Then
--   $$P(N_x < n) \le P(N_y < n), \qquad n = 1, 2, \dots, \text{ and } n = \infty.$$
--
--   **Formalization Note** The statement is formulated for the laws `Kernel.trajMeasure P₁ p` and `trajMeasure Q₁ q` of the two sequences. With 0-based coordinates, the event $\{N_x < n\}$ for $n = m + 1$ is $\{\exists\, i < m : x_i \in A\}$, so the first conjunct is stated for all `m : ℕ` (covering $n = 1, 2, \dots$), and the event $\{N_x < \infty\}$ is $\{\exists\, i : x_i \in A\}$ (second conjunct).
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Corollary 1 (ii), p. 904 (PDF p. 6)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem corollary1_ii {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π _ : Iic n, E, x ≤ y → StochLE (p n x) (q n y))
    (A : Set E) (hA : MeasurableSet A) (hAup : IsUpperSet A) :
    (∀ m : ℕ, Kernel.trajMeasure (X := fun _ => E) P₁ p {x | ∃ i < m, x i ∈ A} ≤
        Kernel.trajMeasure (X := fun _ => E) Q₁ q {x | ∃ i < m, x i ∈ A}) ∧
      Kernel.trajMeasure (X := fun _ => E) P₁ p {x | ∃ i, x i ∈ A} ≤
        Kernel.trajMeasure (X := fun _ => E) Q₁ q {x | ∃ i, x i ∈ A} := by sorry

end StochIneqPO.Comparison
