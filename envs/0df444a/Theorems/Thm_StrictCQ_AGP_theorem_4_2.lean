-- Prove2me | Theorems.Thm_StrictCQ_AGP_theorem_4_2
-- name    : StrictCQ.AGP.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:20.31505+00:00
-- url     : https://prove2.me/theorems/b753028e-1d85-4eab-82ee-6427ea859a74
-- title:
--   Theorem 4.2, p. 7 — AGP-regularity is the weakest strict constraint qualification associated with AGP
-- statement:
--   Let the constraint functions $h_1,\dots,h_m,g_1,\dots,g_p$ of problem (1.1) be continuously differentiable on $\mathbb R^n$, and let $x^*$ be a feasible point. Then
--
--   $$
--   x^*\ \text{is AGP-regular}\iff\text{for every } \mathrm C^1 \text{ objective } f:\ \mathrm{AGP}(-\infty)\text{ at } x^* \implies \text{KKT at } x^*.
--   $$
--
--   Here AGP-regularity is the outer semicontinuity at $(x^*,0)$ of $(x,\varepsilon)\mapsto N_{\Omega(x,-\infty)}(x+\varepsilon)$ (Definition 4.1), and AGP($-\infty$) asks for $x^k\to x^*$ with $P_{\Omega(x^k,-\infty)}(x^k-\nabla f(x^k))-x^k\to0$ (4.1).
--
--   The forward implication says AGP-regularity is a strict constraint qualification for AGP; the backward implication says every property of the constraints under which AGP implies KKT for all objectives implies AGP-regularity, so it is the weakest one.
--
--   **Formalization Note** The paper's "AGP" is AGP($\gamma$) for $\gamma\in[-\infty,0)$, which Martínez and Svaiter showed to be independent of $\gamma$; this paper does not prove that. The goal pins $\gamma=-\infty$. The forward direction for every $\gamma\in[-\infty,0)$ is the separate theorem `agp_regular_agp_implies_kkt`, and the backward direction for $\gamma=-\infty$ is the strongest form, since its hypothesis is only about $\gamma=-\infty$. KKT is in multiplier form; the objective is quantified inside the equivalence, for fixed constraints and fixed $x^*$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 7, Theorem 4.2

import Mathlib
import Definitions.Def_StrictCQ_AGP_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- Theorem 4.2: AGP-regularity is the weakest strict constraint qualification associated with
AGP. AGP is AGP(-∞). -/
theorem theorem_4_2 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    C.AGPRegular xs ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → C.AGP ⊥ f xs → C.IsKKT f xs := by sorry

end StrictCQ.AGP
