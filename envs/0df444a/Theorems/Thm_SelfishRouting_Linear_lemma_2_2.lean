-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_2_2
-- name    : SelfishRouting.Linear.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:04.912177+00:00
-- url     : https://prove2.me/theorems/c5e27c53-7cf5-4311-b62a-cb7a2c7cc958
-- title:
--   Lemma 2.2 — a feasible flow is at Nash equilibrium iff every used path has minimum latency
-- statement:
--   Consider the routing model with routes given by $0/1$ edge incidences, commodities $i$ with positive rates $r_i>0$, and edge latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$. Let $f$ be a route flow. Then $f$ is at Nash equilibrium (Definition 2.1) if and only if $f$ is feasible and for every commodity $i$ and routes $P_1,P_2\in\mathcal P_i$ with $f_{P_1}>0$,
--   $$\ell_{P_1}(f)\le \ell_{P_2}(f).$$
--
--   The right-hand side is the Wardrop condition. This lemma turns the deviation-based Definition 2.1 into a condition on the latencies at $f$ alone, which is what all of the paper's later arguments use.
--
--   **Formalization Note** The right-hand side is the published `KellyStochasticNetworks.IsWardropEquilibrium` (which includes feasibility). Continuity replaces the paper's differentiability (footnote 3, p. 7, licenses this), which weakens a hypothesis; the latency hypotheses are imposed only on $[0,\infty)$, where flows live. Definition 2.1 is formalized with $P_1\neq P_2$ and $0<\delta\le f_{P_1}$ (see the definition item). Routes are $0/1$ incidence columns rather than simple paths, a disclosed generalization.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 7, Lemma 2.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- Lemma 2.2 (Roughgarden–Tardos, p. 7): for latencies that are nonnegative, nondecreasing
and continuous on `[0, ∞)`, a flow is at Nash equilibrium (Definition 2.1) if and only if it
is feasible and every route carrying positive flow has latency at most that of any route
serving the same commodity (the Wardrop condition). -/
theorem lemma_2_2 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) :
    SelfishRouting.Bicriteria.IsNashFlow A s ℓ rate x ↔ IsWardropEquilibrium A s ℓ rate x := by sorry

end SelfishRouting.Linear
