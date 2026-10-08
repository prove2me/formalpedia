-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_4_1_a
-- name    : SelfishRouting.Linear.lemma_4_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:05.754102+00:00
-- url     : https://prove2.me/theorems/978490d3-2de5-429d-a04e-1cad96e801b2
-- title:
--   Lemma 4.1(a) — Nash flows for linear latencies: $\sum_{e\in P}(a_ef_e+b_e)\le\sum_{e\in P'}(a_ef_e+b_e)$ on used paths
-- statement:
--   Let every edge have a linear latency $\ell_e(x)=a_ex+b_e$ with $a_e,b_e\ge 0$, let the rates be positive, and let the route incidences be $0/1$. Then a flow $f$ is at Nash equilibrium if and only if $f$ is feasible and for each commodity $i$ and routes $P,P'\in\mathcal P_i$ with $f_P>0$,
--   $$\sum_{e\in P}\big(a_ef_e+b_e\big)\le\sum_{e\in P'}\big(a_ef_e+b_e\big).$$
--
--   This is Lemma 2.2 specialized to linear latencies, written out in the coefficients; it is used, together with part (b), to show that half of a Nash flow is optimal for half the rates.
--
--   **Formalization Note** The page prints $\sum_{e\in P}a_ef_e+b_e$; since $\ell_P(f)=\sum_{e\in P}\ell_e(f_e)$, this means $\sum_{e\in P}(a_ef_e+b_e)$, and the sum ranges over the edges $e$ with incidence $1$ in route $P$. Feasibility is part of Definition 2.1, so it appears on the right-hand side. The paper states the lemma for linear latencies; $a_e,b_e\ge 0$ is the standing assumption of §4 (p. 14). Routes are $0/1$ incidence columns (a disclosed generalization).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 14–15, Lemma 4.1(a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- Lemma 4.1(a) (p. 15): with latencies `ℓ_e(x) = a_e x + b_e`, a flow is at Nash equilibrium
iff it is feasible and, for every commodity and routes `P, P'` serving it with `f_P > 0`,
`∑_{e ∈ P} (a_e f_e + b_e) ≤ ∑_{e ∈ P'} (a_e f_e + b_e)`. -/
theorem lemma_4_1_a {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (x : Fin R → ℝ) :
    SelfishRouting.Bicriteria.IsNashFlow A s (linLatency a b) rate x ↔
      (x ∈ wardropFeasible s rate ∧
        ∀ P P' : Fin R, s P = s P' → 0 < x P →
          ∑ j ∈ Finset.univ.filter (fun j => A j P = 1), (a j * linkFlow A x j + b j) ≤
            ∑ j ∈ Finset.univ.filter (fun j => A j P' = 1), (a j * linkFlow A x j + b j)) := by sorry

end SelfishRouting.Linear
