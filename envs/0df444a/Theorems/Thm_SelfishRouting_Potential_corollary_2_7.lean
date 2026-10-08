-- Prove2me | Theorems.Thm_SelfishRouting_Potential_corollary_2_7
-- name    : SelfishRouting.Potential.corollary_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:12.016921+00:00
-- url     : https://prove2.me/theorems/7744f6c1-dbc1-48c4-a66a-beb1b8c3f94f
-- title:
--   Corollary 2.7 — if $x\,\ell_e(x)\le\alpha\int_0^x\ell_e$, a Nash flow costs at most $\alpha$ times any feasible flow
-- statement:
--   Consider a routing instance with latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$, routes given by $0/1$ edge–route incidence columns, and positive rates $r_i$. Write $C(f)=\sum_P\ell_P(f)f_P$ for the cost of a flow. Let $\alpha\ge1$ be a constant such that
--   $$x\cdot\ell_e(x)\le\alpha\int_0^x\ell_e(t)\,dt\qquad\text{for all edges } e \text{ and all real } x>0 .$$
--
--   **Corollary 2.7.** If $f$ is a flow at Nash equilibrium and $f^*$ is any feasible flow, then
--   $$C(f)\le\alpha\,C(f^*).$$
--   In particular $\rho(G,r,\ell)=C(f)/C(f^*)\le\alpha$ for an optimal flow $f^*$.
--
--   The hypothesis says that the latencies are "not too steep": the Beckmann potential $\sum_e\int_0^{f_e}\ell_e$, which a Nash flow minimizes, is within a factor $\alpha$ of the true cost.
--
--   **Formalization Note** The paper's conclusion $\rho(G,r,\ell)\le\alpha$ is stated as the inequality $C(f)\le\alpha C(f^*)$ for every feasible $f^*$, which is what the proof's chain of inequalities (pp. 10–11) establishes and which implies the ratio bound for an optimal $f^*$; this avoids dividing by a cost that may be $0$. The hypothesis is quantified over $x>0$ only, as printed, and $\alpha\ge1$ is kept as printed. Continuity on $[0,\infty)$ makes $\int_0^x\ell_e$ an honest integral. Routes are $0/1$ incidence columns (a generalization of simple paths); continuity replaces differentiability (footnote 3, p. 7).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 10, Corollary 2.7

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Potential_Model

open KellyStochasticNetworks

namespace SelfishRouting.Potential

theorem corollary_2_7 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (α : ℝ) (hα1 : 1 ≤ α)
    (hα : ∀ j t, 0 < t → t * ℓ j t ≤ α * ∫ u in (0:ℝ)..t, ℓ j u)
    (x y : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x) (hy : y ∈ wardropFeasible s rate) :
    SelfishRouting.Bicriteria.cost A ℓ x ≤ α * SelfishRouting.Bicriteria.cost A ℓ y := by sorry

end SelfishRouting.Potential
