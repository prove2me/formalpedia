-- Prove2me | Theorems.Thm_SelfishRouting_Potential_corollary_2_8
-- name    : SelfishRouting.Potential.corollary_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:12.456189+00:00
-- url     : https://prove2.me/theorems/546ac088-a96e-4b5f-b2f8-1501d5978179
-- title:
--   Corollary 2.8 — with polynomial latencies of degree $p$ and nonnegative coefficients, $\rho(G,r,\ell)\le p+1$
-- statement:
--   Consider a routing instance whose routes are given by $0/1$ edge–route incidence columns, each serving one commodity $i$ with positive rate $r_i$, and whose latency functions are polynomials
--   $$\ell_e(x)=\sum_{i=0}^{p}a_{e,i}\,x^i$$
--   for a positive integer $p$ and nonnegative reals $a_{e,i}$ ($0\le i\le p$). Write $C(f)=\sum_P\ell_P(f)f_P$ for the cost of a flow.
--
--   **Corollary 2.8.** If $f$ is a flow at Nash equilibrium (Definition 2.1) and $f^*$ is any feasible flow, then
--   $$C(f)\le(p+1)\,C(f^*).$$
--   Equivalently, $\rho(G,r,\ell)\le p+1$: selfish routing costs at most $p+1$ times the optimum. For linear latencies ($p=1$) this gives the factor $2$, later improved to $4/3$ in §4 of the paper.
--
--   **Formalization Note** The paper's $\rho(G,r,\ell)=C(f)/C(f^*)\le p+1$, with $f^*$ optimal, is stated as an inequality against every feasible flow, which is equivalent once an optimal flow exists and avoids dividing by a cost that may be $0$. The degree $p$ is a common upper bound: $a_{e,p}=0$ is allowed. Coefficients are required nonnegative only for $i\le p$, the ones that occur. Polynomials with nonnegative coefficients are nonnegative, nondecreasing and continuous on $[0,\infty)$, so no other latency hypothesis is needed. Routes are $0/1$ incidence columns, a generalization of the simple paths of a graph.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 11, Corollary 2.8

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Potential_Model
import Definitions.Def_SelfishRouting_Potential_PolyLatency

open KellyStochasticNetworks

namespace SelfishRouting.Potential

theorem corollary_2_8 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (p : ℕ) (hp : 0 < p) (a : Fin J → ℕ → ℝ) (ha : ∀ j i, i ≤ p → 0 ≤ a j i)
    (x y : Fin R → ℝ) (hx : IsNashFlow A s (polyLatency p a) rate x)
    (hy : y ∈ wardropFeasible s rate) :
    SelfishRouting.Bicriteria.cost A (polyLatency p a) x ≤ ((p : ℝ) + 1) * SelfishRouting.Bicriteria.cost A (polyLatency p a) y := by sorry

end SelfishRouting.Potential
