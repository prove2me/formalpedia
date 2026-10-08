-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_4_1_b
-- name    : SelfishRouting.Linear.lemma_4_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:47.891102+00:00
-- url     : https://prove2.me/theorems/07b524a4-9ad4-491b-b877-328da4097046
-- title:
--   Lemma 4.1(b) — optimal flows for linear latencies: $\sum_{e\in P}(2a_ef^*_e+b_e)\le\sum_{e\in P'}(2a_ef^*_e+b_e)$ on used paths
-- statement:
--   Let every edge have a linear latency $\ell_e(x)=a_ex+b_e$ with $a_e,b_e\ge 0$, let the rates be positive, and let the route incidences be $0/1$. Then a flow $f^*$ is (globally) optimal, i.e. feasible with $C(f^*)\le C(g)$ for every feasible $g$, if and only if $f^*$ is feasible and for each commodity $i$ and routes $P,P'\in\mathcal P_i$ with $f^*_P>0$,
--   $$\sum_{e\in P}\big(2a_ef^*_e+b_e\big)\le\sum_{e\in P'}\big(2a_ef^*_e+b_e\big).$$
--
--   This is the first-order (Karush–Kuhn–Tucker) characterization of the convex quadratic program $\min\sum_e a_ef_e^2+b_ef_e$ over feasible flows: a flow is optimal exactly when it is at Nash equilibrium for the marginal costs $\ell^*_e(x)=2a_ex+b_e$. Both directions are used in the proof of Theorem 4.5.
--
--   **Formalization Note** "Globally optimal" is optimality over all flows feasible for the same rates, not local optimality. The sums range over the edges with incidence $1$ in each route; the page's $\sum_{e\in P}2a_ef^*_e+b_e$ means $\sum_{e\in P}(2a_ef^*_e+b_e)$. Routes are $0/1$ incidence columns (a disclosed generalization).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 14–15, Lemma 4.1(b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- Lemma 4.1(b) (p. 15): with latencies `ℓ_e(x) = a_e x + b_e`, `a_e, b_e ≥ 0`, a flow is
(globally) optimal iff it is feasible and, for every commodity and routes `P, P'` serving it
with `f*_P > 0`, `∑_{e ∈ P} (2 a_e f*_e + b_e) ≤ ∑_{e ∈ P'} (2 a_e f*_e + b_e)`. -/
theorem lemma_4_1_b {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (xstar : Fin R → ℝ) :
    IsOptimalFlow A s (linLatency a b) rate xstar ↔
      (xstar ∈ wardropFeasible s rate ∧
        ∀ P P' : Fin R, s P = s P' → 0 < xstar P →
          ∑ j ∈ Finset.univ.filter (fun j => A j P = 1), (2 * a j * linkFlow A xstar j + b j) ≤
            ∑ j ∈ Finset.univ.filter (fun j => A j P' = 1),
              (2 * a j * linkFlow A xstar j + b j)) := by sorry

end SelfishRouting.Linear
