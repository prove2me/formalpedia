-- Prove2me | Theorems.Thm_SendSplit_Existence_concave_sandwich
-- name    : SendSplit.Existence.concave_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:12:50.130029+00:00
-- url     : https://prove2.me/theorems/5547a088-380b-4518-8702-4fb78824dfa6
-- title:
--   Proof of Theorem 1, p. 639 — $\tfrac12 c(2x) + \tfrac12 c(2\theta y) \le c(x+\theta y) \le c(x) + c(\theta y)$
-- statement:
--   Let $G$ be a graph with arc costs $c_{ij}$ concave on $[0,\infty)$ and $c_{ij}(0) = 0$. For all preflows $x, y$ and every $\theta \ge 0$,
--
--   $$\tfrac12 c(2x) + \tfrac12 c(2\theta y) \;\le\; c(x + \theta y) \;\le\; c(x) + c(\theta y).$$
--
--   The left inequality is concavity of $c$ at the midpoint of $2x$ and $2\theta y$; the right one is subadditivity, which follows from concavity and $c_{ij}(0) = 0$. With it, $c(x + \theta y)$ is bounded below in $\theta \ge 0$ if and only if $c(\theta y)$ is.
--
--   **Formalization Note** The paper states the display for an extreme flow $x$ and a simple circulation $y$; it holds for all preflows, and this general form is stated.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, proof of Theorem 1

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

theorem concave_sandwich {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (x y : Fin n → Fin n → ℝ) (hx : IsPreflow G x)
    (hy : IsPreflow G y) (θ : ℝ) (hθ : 0 ≤ θ) :
    (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * x i j)
        + (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * (θ * y i j))
        ≤ flowCost G c (fun i j => x i j + θ * y i j) ∧
      flowCost G c (fun i j => x i j + θ * y i j)
        ≤ flowCost G c x + flowCost G c (fun i j => θ * y i j) := by sorry

end SendSplit.Existence
