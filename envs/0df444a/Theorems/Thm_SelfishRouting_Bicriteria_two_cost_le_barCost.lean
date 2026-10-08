-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_two_cost_le_barCost
-- name    : SelfishRouting.Bicriteria.two_cost_le_barCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:52.637785+00:00
-- url     : https://prove2.me/theorems/9bc3e7a5-6ede-443c-a798-67d8414f5e4d
-- title:
--   Proof of Theorem 3.1, second display, p. 13 — $\sum_P \bar\ell_P(f^*) f^*_P \ge 2C(f)$
-- statement:
--   Consider an instance with $0/1$ edge–route incidence matrix $A$, commodities with rates $r_i > 0$, and edge latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$. Let $f$ be a Nash flow for the rates $r$, let $f^*$ be a flow feasible for the doubled rates $2r$, and let $\bar\ell$ be the modified latencies built from the edge flows of $f$, with route latencies $\bar\ell_P(f^*) = \sum_{e \in P} \bar\ell_e(f^*_e)$. Then
--   $$
--   \sum_{P} \bar\ell_P(f^*)\, f^*_P \ge 2\,C(f).
--   $$
--
--   This is the lower half of the proof of Theorem 3.1: under $\bar\ell$ every route of commodity $i$ costs at least the common Nash latency $L_i(f)$, whatever the flow.
--
--   **Formalization Note.** The conclusion is stated without $L_i(f)$, which is a step of the proof. Routes are $0/1$ incidence columns, continuity replaces differentiability, and the latency hypotheses are on $[0,\infty)$ only.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 13, proof of Theorem 3.1, second display

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Proof of Theorem 3.1, second display (p. 13): for a Nash flow `f` and a flow `f*`
feasible for twice the rates, `∑_P ℓ̄_P(f*) f*_P ≥ 2 C(f)`. -/
theorem two_cost_le_barCost {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x y : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x)
    (hy : y ∈ wardropFeasible s (fun i => 2 * rate i)) :
    2 * cost A ℓ x ≤
      ∑ r, (∑ j, barLatency ℓ (linkFlow A x) j (linkFlow A y j) * A j r) * y r := by sorry

end SelfishRouting.Bicriteria
