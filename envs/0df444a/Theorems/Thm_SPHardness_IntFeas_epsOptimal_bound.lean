-- Prove2me | Theorems.Thm_SPHardness_IntFeas_epsOptimal_bound
-- name    : SPHardness.IntFeas.epsOptimal_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:41.972488+00:00
-- url     : https://prove2.me/theorems/1896be18-e9ee-4c92-87ce-16b8f55fa9a6
-- title:
--   Proof of Theorem 4, pp. 13–14 — every ϵ-optimal decision x of (11) satisfies |x⋆ − x| ≤ 2nϵ
-- statement:
--   Let $(A,b)$ be an instance of the Integer Feasibility Problem with a nonempty polytope $\{\xi\in\mathbb R^n:A\xi\le b\}$ and $n\ge1$, let $x^\star=\max\{\sum_{i=1}^n\max\{\xi_i,1-\xi_i\}:A\xi\le b\}$, and let $\epsilon\ge0$. If $x$ is an $\epsilon$-optimal decision of problem (11), that is, $x$ is feasible and
--   $$\frac{\big|f^\star-\big(x+\mathbb E[Q(x,\tilde\xi)]\big)\big|}{\max\{|f^\star|,1\}}\le\epsilon,$$
--   then
--   $$|x^\star-x|\le 2n\epsilon .$$
--
--   This converts relative accuracy of the objective into absolute accuracy of the decision; with $\epsilon<\epsilon'/4n$ it gives $|x^\star-x|<\epsilon'/2$, half the gap of the dichotomy for $x^\star$.
--
--   **Formalization Note.** $f^\star$ is the infimum of the objective over feasible decisions; $\mathbb E$ is the integral over $[0,1]^n$ with Lebesgue measure. The hypotheses $n\ge1$ (used in $\max\{1,f^\star\}\le 2n$) and $\epsilon\ge0$ (implicit in $\epsilon$-optimality) are added. The page's strict "$<\epsilon'/2$" is the combination of this bound with $\epsilon<\epsilon'/4n$ and is part of Theorem 4.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), §3, proof of Theorem 4, pp. 13–14

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

namespace SPHardness.IntFeas

theorem epsOptimal_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (hn : 1 ≤ n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (x : ℝ) (hx : IsEpsOptimal A b ε x) :
    |xStar A b - x| ≤ 2 * n * ε := by sorry

end SPHardness.IntFeas
