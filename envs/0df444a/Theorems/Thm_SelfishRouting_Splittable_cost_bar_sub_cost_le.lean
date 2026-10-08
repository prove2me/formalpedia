-- Prove2me | Theorems.Thm_SelfishRouting_Splittable_cost_bar_sub_cost_le
-- name    : SelfishRouting.Splittable.cost_bar_sub_cost_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:09.78399+00:00
-- url     : https://prove2.me/theorems/16745b64-7823-4e86-a616-a1eab6c4f211
-- title:
--   Proof of Theorem 5.4, p. 20 — evaluating $f^*$ with $\bar\ell$ increases its cost by at most $C(f)$
-- statement:
--   Let latency functions $\ell_e$ be nonnegative, nondecreasing and continuous on $[0,\infty)$, let $f$ and $f^*$ be flows with nonnegative route flows, and let $\bar\ell$ be the modified latency functions built from the edge flows $f_e$ of $f$. Then the cost of $f^*$ with respect to $\bar\ell$ exceeds its cost with respect to $\ell$ by at most $C(f)$:
--
--   $$\sum_P \bar\ell_P(f^*)\,f^*_P - C(f^*)\;\le\; C(f).$$
--
--   This is the first step of the proof of Theorem 5.4, which refers back to the first display of p. 13:
--   $$\sum_e \bar\ell_e(f^*_e)f^*_e - C(f^*) = \sum_{e\in E} f^*_e\bigl(\bar\ell_e(f^*_e)-\ell_e(f^*_e)\bigr)\le \sum_{e\in E}\ell_e(f_e)f_e = C(f).$$
--   Together with the lower bound on the $\bar\ell$-cost of any flow feasible for twice the rates it yields Theorem 5.4.
--
--   **Formalization Note** The bound is stated for any two flows with nonnegative route flows, not only for a Nash flow $f$ and a flow $f^*$ feasible for $2r$; the page's argument uses nothing else, so this is a mild generalization. The $\bar\ell$-cost is written in path form $\sum_P\bar\ell_P(f^*)f^*_P$, which equals the edge form. Routes are $0/1$ incidence columns (a generalization of simple paths); continuity replaces differentiability (footnote 3, p. 7).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 20, proof of Theorem 5.4, first paragraph (referring to the first display of p. 13)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Splittable_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

namespace SelfishRouting.Splittable

open KellyStochasticNetworks

theorem cost_bar_sub_cost_le {J R : ℕ} (A : Fin J → Fin R → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x y : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (hy : ∀ r, 0 ≤ y r) :
    SelfishRouting.Bicriteria.cost A (SelfishRouting.Bicriteria.barLatency ℓ (linkFlow A x)) y - SelfishRouting.Bicriteria.cost A ℓ y ≤ SelfishRouting.Bicriteria.cost A ℓ x := by sorry

end SelfishRouting.Splittable
