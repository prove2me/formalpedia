-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_theorem_3_2
-- name    : SelfishRouting.Bicriteria.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:34.3828+00:00
-- url     : https://prove2.me/theorems/660dcbfd-7265-4fcf-bd35-ad5143ee2409
-- title:
--   Theorem 3.2 — $C(f) \le \frac{1}{\gamma} C(f^*)$ for $f^*$ feasible for $(1+\gamma)r$
-- statement:
--   Consider a routing instance as in Theorem 3.1: a $0/1$ edge–route incidence matrix, rates $r_i > 0$, and edge latency functions that are nonnegative, nondecreasing and continuous on $[0,\infty)$. Let $\gamma > 0$. If $f$ is a flow at Nash equilibrium for the rates $r$ and $f^*$ is any flow feasible for the rates $(1+\gamma)r$, then
--   $$
--   C(f) \le \frac{1}{\gamma}\, C(f^*).
--   $$
--
--   For $\gamma = 1$ this is Theorem 3.1. The paper notes that the bound is essentially tight for every $\gamma$.
--
--   **Formalization Note.** The page does not quantify $\gamma$; the factor $1/\gamma$ requires $\gamma > 0$, which is assumed. Same model conventions as Theorem 3.1.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 14, Theorem 3.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Theorem 3.2 (p. 14): for `γ > 0`, the cost of a Nash flow for rates `r` is at most
`1/γ` times the cost of any flow feasible for the rates `(1 + γ) r`. -/
theorem theorem_3_2 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (γ : ℝ) (hγ : 0 < γ)
    (x y : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x)
    (hy : y ∈ wardropFeasible s (fun i => (1 + γ) * rate i)) :
    cost A ℓ x ≤ 1 / γ * cost A ℓ y := by sorry

end SelfishRouting.Bicriteria
