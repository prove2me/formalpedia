-- Prove2me | Theorems.Thm_SelfishRouting_Linear_theorem_4_5
-- name    : SelfishRouting.Linear.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:43.218032+00:00
-- url     : https://prove2.me/theorems/b275f8ea-baff-45af-a3fa-475becc2ac6a
-- title:
--   Theorem 4.5 — with linear latencies, $\rho(G,r,\ell)\le 4/3$: a Nash flow costs at most $4/3$ times any feasible flow
-- statement:
--   Let $(G,r,\ell)$ be an instance with linear latency functions $\ell_e(x)=a_ex+b_e$, $a_e,b_e\ge 0$, positive rates $r_i>0$, and $0/1$ route incidences. Let $f$ be a flow at Nash equilibrium. Then for every flow $f^*$ feasible for the rates $r$,
--   $$C(f)\ \le\ \tfrac43\,C(f^*).$$
--
--   In the paper's notation, $\rho(G,r,\ell)=C(f)/C(f^*)\le 4/3$ for an optimal flow $f^*$: with linear latencies, selfish routing costs at most a third more than optimal routing. Figure 3 shows the constant is attained.
--
--   **Formalization Note** The ratio $\rho$ (p. 10) is not formed: $C(f^*)$ can be $0$, where Lean's division would return $0$. The statement is the proof's last line ("the cost of any flow $f^*$ feasible for $(G,r,\ell)$ satisfies … $C(f^*)\ge\frac34C(f)$", p. 17) for every feasible $f^*$, which implies $\rho\le 4/3$ whenever an optimal flow has positive cost and gives $C(f)=0$ when it has cost $0$. Definition 2.1 is formalized with $P_1\neq P_2$ and $0<\delta\le f_{P_1}$. Routes are $0/1$ incidence columns rather than the simple paths of a directed graph; the paper's setting is one instance, so this is a disclosed generalization.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 17, Theorem 4.5 (ρ defined on p. 10)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- Theorem 4.5 (p. 17): if `(G, r, ℓ)` has linear latency functions `ℓ_e(x) = a_e x + b_e`
with `a_e, b_e ≥ 0`, then `ρ(G, r, ℓ) ≤ 4/3`, stated without a ratio: the cost of a flow at
Nash equilibrium is at most `4/3` times the cost of every feasible flow. -/
theorem theorem_4_5 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (x : Fin R → ℝ) (hx : SelfishRouting.Bicriteria.IsNashFlow A s (linLatency a b) rate x)
    (y : Fin R → ℝ) (hy : y ∈ wardropFeasible s rate) :
    SelfishRouting.Bicriteria.cost A (linLatency a b) x ≤ 4 / 3 * SelfishRouting.Bicriteria.cost A (linLatency a b) y := by sorry

end SelfishRouting.Linear
