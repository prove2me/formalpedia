-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_4_3_a
-- name    : SelfishRouting.Linear.lemma_4_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:51.000323+00:00
-- url     : https://prove2.me/theorems/5267cc9e-9df0-4fc3-b702-287457dbc2ae
-- title:
--   Lemma 4.3(a) — if $f$ is a Nash flow for $(G,r,\ell)$ with linear latencies, then $f/2$ is optimal for $(G,r/2,\ell)$
-- statement:
--   Let every edge have a linear latency $\ell_e(x)=a_ex+b_e$ with $a_e,b_e\ge 0$, let the rates $r_i$ be positive and the route incidences $0/1$, and let $f$ be a flow at Nash equilibrium for the rates $r$. Then the flow $f/2$, with $(f/2)_P=f_P/2$, is optimal for the rates $r/2$:
--   $$C(f/2)\le C(g)\quad\text{for every flow } g \text{ feasible for } r/2,$$
--   and $f/2$ is itself feasible for $r/2$.
--
--   This is the first step of the proof of Theorem 4.5: half of a selfish flow is a socially optimal flow for half the traffic.
--
--   **Formalization Note** The rates $r/2$ are $i\mapsto r_i/2$ and the flow $f/2$ is $P\mapsto f_P/2$. Routes are $0/1$ incidence columns (a disclosed generalization).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 15, Lemma 4.3(a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

/-- Lemma 4.3(a) (p. 15): with linear latencies, if `f` is at Nash equilibrium for the rates
`r`, then `f/2` is optimal for the rates `r/2`. -/
theorem lemma_4_3_a {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (x : Fin R → ℝ) (hx : SelfishRouting.Bicriteria.IsNashFlow A s (linLatency a b) rate x) :
    IsOptimalFlow A s (linLatency a b) (fun i => rate i / 2) (fun r => x r / 2) := by sorry

end SelfishRouting.Linear
