-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_prop1_iterProd_le
-- name    : StochIneqPO.Comparison.prop1_iterProd_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:26:12.266203+00:00
-- url     : https://prove2.me/theorems/6d040499-de45-419e-83fc-4a0cc4559319
-- title:
--   Proposition 1 — $P_1 * p_2 * \cdots * p_n \prec Q_1 * q_2 * \cdots * q_n$ when $P_1 \prec Q_1$ and the kernels are ordered
-- statement:
--   Let $E_1, E_2, \dots, E_n$ be partially ordered Polish spaces, with $E^{i} = E_1 \times \cdots \times E_i$ carrying the product topology and the coordinatewise order. Let $P_1, Q_1$ be probability measures on $E_1$ with $P_1 \prec Q_1$, and for $i = 2, \dots, n$ let $p_i, q_i$ be stochastic kernels from $E^{i-1}$ to $E_i$ such that
--   $$p_i(x^{i-1}, \cdot) \prec q_i(y^{i-1}, \cdot) \qquad \text{whenever } x^{i-1} \le y^{i-1}. \tag{1}$$
--   Then
--   $$P_1 * p_2 * \cdots * p_n \;\prec\; Q_1 * q_2 * \cdots * q_n \tag{2}$$
--   as probability measures on the partially ordered Polish space $E^{n}$.
--
--   This is the finite-horizon comparison of two processes built from ordered initial laws and ordered transition kernels; Theorem 2 passes to the limit $n \to \infty$.
--
--   **Formalization Note** Indices are 0-based: the paper's $E_i$ is `E (i - 1)`, the paper's kernel $p_i$ ($i \ge 2$) is `p (i - 2)`, and the paper's $n$ is `m + 1`, so the conclusion is `StochLE (iterProd P₁ p m) (iterProd Q₁ q m)`. Hypothesis (1) is required exactly for the kernels that enter the product (`n < m` in Lean), pointwise for all ordered pairs of histories. The kernel families are indexed by all of $\mathbb N$ (Mathlib's Ionescu-Tulcea API); kernels beyond the horizon play no role.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proposition 1, eqs. (1)–(2), pp. 901–902 (PDF pp. 3–4)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_Comparison_iterProd

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem prop1_iterProd_le {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)] [∀ n, PolishSpace (E n)]
    [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)] [∀ n, PartialOrder (E n)]
    [∀ n, OrderClosedTopology (E n)]
    (P₁ Q₁ : Measure (E 0)) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1)))
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (m : ℕ) (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n < m, ∀ x y : Π i : Iic n, E i, x ≤ y → StochLE (p n x) (q n y)) :
    StochLE (iterProd P₁ p m) (iterProd Q₁ q m) := by sorry

end StochIneqPO.Comparison
