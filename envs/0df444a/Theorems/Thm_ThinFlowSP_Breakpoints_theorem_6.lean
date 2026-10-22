-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_theorem_6
-- name    : ThinFlowSP.Breakpoints.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:36.288079+00:00
-- url     : https://prove2.me/theorems/d6104cef-c57c-458e-a656-214cedc490c9
-- title:
--   Theorem 6, pp. 5–6 — normalized thin flows with resetting are the normalized solutions of (LCP)
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$, let $\nu \in \mathbb R^{A'}_{>0}$ be capacities, $\nu'_0 \ge 0$ an inflow rate and $\ell'_0 \ge 0$ a label, and let $M$ be the matrix of (LCP). For $\ell' \in \mathbb R^V$, $x' \in \mathbb R^{A'}$ and $y' \in \mathbb R^{A'\setminus A^*}$ the following are equivalent:
--
--   1. $z' = (\ell', x', y')$ solves
--   $$z \ge 0,\qquad Mz - \ell'_0\mathbb 1_s - \nu'_0\mathbb 1_t \ge 0,\qquad z^\top(Mz - \ell'_0\mathbb 1_s - \nu'_0\mathbb 1_t) = 0,$$
--   and $\ell'_w \ge \min_{v\in N^-(w)} \ell'_v$ for every $w \ne s$ that no resetting arc enters;
--   2. $x'$ is a static $s$–$t$-flow of value $\nu'_0$ with corresponding labels $\ell'$ (Definition 4), $\ell'_s = \ell'_0$, and $y'_a = [\ell'_v - x'_a/\nu_a]_+$ for every $a = (v,w) \in A'\setminus A^*$.
--
--   The theorem turns the non-linear conditions of Definition 4 into a linear complementarity problem, which is the basis of the existence proof (Theorem 13) and of the parametric analysis (Proposition 17).
--
--   **Formalization Note** $z'$ is the concatenation `Sum.elim l (Sum.elim x y)`. The normalization constraint "$\ell'_w \ge \min_{v\in N^-(w)}\ell'_v$" is written as "some arc $(v, w)$ has $\ell'_v \le \ell'_w$", which is the same for the non-empty $N^-(w)$ of a shortest path graph. $[\cdot]_+ = \max(\cdot, 0)$. The hypothesis $s \ne t$ is the paper's standing assumption that $s$ is the source and $t$ the sink of the commodity (§2).
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, pp. 5–6, Theorem 6

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem theorem_6 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (nu0 l0 : ℝ) (hnu0 : 0 ≤ nu0) (hl0 : 0 ≤ l0)
    (l : G.V → ℝ) (x : G.A → ℝ) (y : {a : G.A // a ∉ Astar} → ℝ) :
    (SolvesLCP (lcpMatrix G Astar ν) (lcpRhs G Astar nu0 l0) (Sum.elim l (Sum.elim x y)) ∧
      ∀ w, w ≠ G.s → (∀ a, G.head a = w → a ∉ Astar) →
        ∃ a, G.head a = w ∧ l (G.tail a) ≤ l w) ↔
    (IsStaticFlow G x nu0 ∧ IsThinFlowLabels G Astar ν x l ∧ l G.s = l0 ∧
      ∀ b : {a : G.A // a ∉ Astar}, y b = max (l (G.tail b.1) - x b.1 / ν b.1) 0) := by sorry

end ThinFlowSP.Breakpoints
