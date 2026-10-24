-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_lp_well_posed
-- name    : ProviderGuarantee.Bound.lp_well_posed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:35.251697+00:00
-- url     : https://prove2.me/theorems/3fd939a8-857a-4f0c-8ca8-9ae1bc05c1cb
-- title:
--   Proof of Theorem 1, p. 38 — the linear program (14) is feasible, its objective is at most 1, and its value lies in [0, 1]
-- statement:
--   Let $n \ge 1$ and let $\gamma \in \mathbb R^n$ have positive entries. Consider the linear program (14) of p. 38 in the variables $x, y \in \mathbb R^n$ and $w \in \mathbb R^{n\times n}$: maximize $\sum_i \gamma_i x_i - \sum_i \gamma_i y_i + \sum_i \sum_j w_{ij}(\gamma_i - \gamma_j)$ subject to $\sum_i \gamma_i x_i + \sum_i \sum_j w_{ij}\gamma_i = 1$, $x_i + w_{ij} - \sum_k w_{kj} - y_j \le 0$ for all $i, j$, and $x, y, w \ge 0$. Then:
--   1. the program has a feasible point;
--   2. every feasible point has objective value at most $1$:
--   $$\sum_{i=1}^n \gamma_i x_i - \sum_{i=1}^n \gamma_i y_i + \sum_{i=1}^n \sum_{j=1}^n w_{ij}(\gamma_i - \gamma_j) \le 1;$$
--   3. its optimal value $V(\gamma)$ satisfies $0 \le V(\gamma) \le 1$.
--
--   The page states that (14) is a linear program with an objective bounded above by $1$, and uses this to invoke strong duality; feasibility and the range $[0,1]$ make the optimal value a well-defined number (the page's $f(\gamma) : [\gamma_{\min}, \gamma_{\max}]^n \to [0, 1]$, p. 38).
--
--   **Formalization Note** $V(\gamma)$ is `lpValue γ`, a real supremum; items 1 and 2 show it is the supremum of a non-empty bounded set rather than a default value.
--
--   Differences from the source:
--   - generalization: γ ∈ [γmin, γmax]^n with 0 < γmin → any γ with γ_i > 0 for every i; reason: every γ in the box has positive entries, so the Lean statement specializes to the page's
--   - reading: N = {1, …, n}, a set of n service providers → 0 < n; reason: with no provider the program (14) is infeasible (its normalization reads 0 = 1), so its value is not defined; the page's LP statements presuppose n ≥ 1
--   - reading: '(14) is a linear program … with an objective function bounded above by 1' → (14) has a feasible point, its objective is ≤ 1 on the feasible set, and 0 ≤ value ≤ 1; reason: the page's appeal to strong duality and its f(γ) : [γmin, γmax]^n → [0, 1] (p. 38) presuppose a feasible program with value in [0, 1]; stating them keeps the real supremum from being a default value
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 38, proof of Theorem 1, (14)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem lp_well_posed {n : ℕ} (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    (∃ x y : Fin n → ℝ, ∃ w : Fin n → Fin n → ℝ, PrimalFeasible γ x y w) ∧
    (∀ (x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ), PrimalFeasible γ x y w →
      primalObj γ x y w ≤ 1) ∧
    0 ≤ lpValue γ ∧ lpValue γ ≤ 1 := by sorry

end ProviderGuarantee.Bound
