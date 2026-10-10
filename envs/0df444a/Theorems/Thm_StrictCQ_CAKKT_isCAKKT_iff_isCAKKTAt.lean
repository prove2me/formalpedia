-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_isCAKKT_iff_isCAKKTAt
-- name    : StrictCQ.CAKKT.isCAKKT_iff_isCAKKTAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:23.827996+00:00
-- url     : https://prove2.me/theorems/8cc5bced-d603-4d65-91d4-6e015a94d541
-- title:
--   (4.12)–(4.13) ⟺ (4.14)–(4.15), p. 9 — the two formulations of CAKKT are equivalent
-- statement:
--   Let $h_i,g_j$ and the objective $f$ be continuously differentiable and $x^*\in\Omega$. Then CAKKT holds at $x^*$ in the form (4.12)–(4.13) if and only if it holds in the form (4.14)–(4.15): there are sequences $x^k\to x^*$, $\lambda^k\in\mathbb R^m$, $\mu^k\in\mathbb R^p_+$ with $\mu^k_j=0$ for $j\notin J(x^*)$ and
--   $$\lim_{k}\nabla f(x^k)+\sum_{i=1}^m\lambda_i^k\nabla h_i(x^k)+\sum_{j\in J(x^*)}\mu_j^k\nabla g_j(x^k)=0,\qquad \lim_k\sum_{i=1}^m|\lambda_i^kh_i(x^k)|+\sum_{j\in J(x^*)}|\mu_j^kg_j(x^k)|=0.$$
--
--   The paper calls the two forms "obviously equivalent"; the second is the one used in the proof of Theorem 4.3.
--
--   **Formalization Note** In both forms $x^k\to x^*$ is part of the condition (see the definition file). The equivalence is not definitional: discarding the multipliers of inactive constraints uses that (4.13) forces $\mu_j^k\to 0$ when $g_j(x^*)<0$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 9, (4.12)–(4.15)

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem isCAKKT_iff_isCAKKTAt {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) :
    C.IsCAKKT f xs ↔ C.IsCAKKTAt f xs := by sorry
end StrictCQ.CAKKT
