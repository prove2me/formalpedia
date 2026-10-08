-- Prove2me | Theorems.Thm_ProductFraming_Nest_proposition_2
-- name    : ProductFraming.Nest.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:01.576674+00:00
-- url     : https://prove2.me/theorems/d34efd17-2521-4eba-a8b9-3efe5469069e
-- title:
--   Proposition 2 — at a worst case of (5), $(U(x)/x)\,\mathbb E[\min(X,x)]$ is constant
-- statement:
--   Fix $m\ge1$ and consider the bound-revealing program (5), with objective $J(U,\Lambda)=\max_{x\in[m]}\frac{U(x)}{x}\mathbb E[\min(X,x)]$ and optimal value $\gamma$. There is an optimal solution $(U,\Lambda)$ of (5) at which
--   $$\gamma\ =\ \frac{U(x)}{x}\,\mathbb E[\min(X,x)]\qquad\text{for all }x\in[m].$$
--
--   This is the worst-case structure of $U$; Proposition 3 uses it to eliminate $U$ from (5).
--
--   **Formalization Note** The paper states the proposition for "the" optimal solution without naming it (p. 10). It is formalized in the existential reading: some optimal solution has a constant $g(x)=\frac{U(x)}{x}\mathbb E[\min(X,x)]$. This is what the rest of the argument uses. The universal reading can fail when $\lambda$ vanishes on part of $[m]$ at the optimum, since the rescaling in the proof is then impossible. Optimality is stated as $J(U,\Lambda)\le J(U',\Lambda')$ for every feasible $(U',\Lambda')$, which also says that the minimum is attained.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 10, Proposition 2 (proof pp. 35–36)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Program

namespace ProductFraming.Nest

open Finset

/-- Proposition 2 (Gallego, Li, Truong, Wang 2020, p. 10), existential reading: problem (5) has an
optimal solution `(U, Λ)` at which `g(x) = (U(x)/x) E[min(X, x)]` is constant on `[m]`, equal
to the optimal value `γ`. -/
theorem proposition_2 (m : ℕ) (hm : 1 ≤ m) :
    ∃ U Λ : ℕ → ℝ, Feasible5 m U Λ ∧
      (∀ U' Λ' : ℕ → ℝ, Feasible5 m U' Λ' → J5 hm U Λ ≤ J5 hm U' Λ') ∧
      ∀ x ∈ Icc 1 m, U x / (x : ℝ) * EminTail Λ x = J5 hm U Λ := by sorry

end ProductFraming.Nest
