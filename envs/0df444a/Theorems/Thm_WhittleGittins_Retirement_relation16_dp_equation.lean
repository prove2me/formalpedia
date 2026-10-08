-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_relation16_dp_equation
-- name    : WhittleGittins.Retirement.relation16_dp_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:55.081748+00:00
-- url     : https://prove2.me/theorems/28d66305-50cf-4149-adcf-6dd88b7832ba
-- title:
--   Relation (16) — F̂(x, 0, M) = M and F̂ = max(M, maxᵢ LᵢF̂)
-- statement:
--   In Whittle's bandit process with per-project horizons $s$, let $\hat F(x, s, M)$ be defined by (13) and $L_i\hat F$ by the extended operator (15). Then $\hat F(x, 0, M) = M$, and $\hat F$ satisfies the dynamic programming equation
--   $$\hat F = \max\big(M,\ \max_i L_i \hat F\big), \qquad (16)$$
--   where the inner maximum runs over the projects $i$ with $s_i > 0$, and $\hat F = M$ when no project can be operated.
--
--   Since $L_i$ lowers $\sum_j s_j$ by one, (16) is recursive in $s$; together with the base case it identifies $\hat F$ with the maximal reward $F$ by induction, which is the first half of Theorem 1.
--
--   **Formalization Note** The maximum over $i$ is restricted to active projects, since a project with $s_i = 0$ may not be operated; when none is active the right-hand side is $M$. Projects are indexed by `Fin N`.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), pp. 147–148 (PDF 5–6), Section 4, relation (16) and the base case F̂(x, 0, M) = M

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Relation (16) (p. 147) with the base case: `F̂(x, 0, M) = M`, and `F̂` satisfies the dynamic
programming equation `F̂ = max(M, maxᵢ Lᵢ F̂)`, the inner maximum over the active projects (and
`F̂ = M` when no project is active). -/
theorem relation16_dp_equation {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (M : ℝ) :
    Fhat B x 0 M = M ∧
      ∀ s : Fin N → ℕ, Fhat B x s M = bellmanMax s M (fun i => LFhat B i x s M) := by sorry

end WhittleGittins.Retirement
