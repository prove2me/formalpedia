-- Prove2me | Theorems.Thm_SelfishRouting_Potential_nash_iff_nlp2_optimal
-- name    : SelfishRouting.Potential.nash_iff_nlp2_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:21.269368+00:00
-- url     : https://prove2.me/theorems/205a8053-07eb-4121-812a-bcb70d775e52
-- title:
--   Proof of Lemma 2.6 — Nash flows are exactly the optimal solutions of (NLP2)
-- statement:
--   Consider a routing instance with latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$, routes given by $0/1$ edge–route incidence columns, and positive rates $r_i$. In the proof of Lemma 2.6 (pp. 9–10) the paper sets $h_e(x)=\int_0^x\ell_e(t)\,dt$ and considers the convex program
--
--   $$\text{(NLP2)}\qquad \min\ \sum_{e\in E}h_e(f_e)\quad\text{subject to}\quad \sum_{P\in\mathcal P_i}f_P=r_i\ \ \forall i,\qquad f_e=\sum_{P\ni e}f_P\ \ \forall e,\qquad f_P\ge0\ \ \forall P,$$
--
--   and observes: "the optimal solutions for (NLP2) are precisely the flows at Nash equilibrium for $(G,r,\ell)$." That is, for every flow $f$,
--   $$f \text{ is at Nash equilibrium}\iff f \text{ is feasible and } \sum_e\int_0^{f_e}\ell_e(t)\,dt\le\sum_e\int_0^{g_e}\ell_e(t)\,dt\ \text{ for every feasible } g .$$
--
--   The objective $\sum_e h_e(f_e)$ is the Beckmann potential of the instance. The direction "Nash $\Rightarrow$ optimal" is what Corollary 2.7 uses; the converse yields existence of Nash flows.
--
--   **Formalization Note** The objective of (NLP2) is the published `KellyStochasticNetworks.wardropObjective` (an interval integral $\int_0^{f_e}\ell_e$); continuity of $\ell_e$ on $[0,\infty)$ makes it an honest Riemann integral. The minimization is over the same feasible set on both sides. The converse direction is related to `KellyStochasticNetworks.wardrop_from_minimizer`, which assumes global continuity and monotonicity and concludes the Wardrop condition rather than Definition 2.1. Routes are $0/1$ incidence columns (a generalization of simple paths); continuity replaces differentiability (footnote 3, p. 7).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 9-10, proof of Lemma 2.6, program (NLP2) and the paragraph following it

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Potential_Model

open KellyStochasticNetworks

namespace SelfishRouting.Potential

theorem nash_iff_nlp2_optimal {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) :
    IsNashFlow A s ℓ rate x ↔
      (x ∈ wardropFeasible s rate ∧
        ∀ y ∈ wardropFeasible s rate, wardropObjective A ℓ x ≤ wardropObjective A ℓ y) := by sorry

end SelfishRouting.Potential
