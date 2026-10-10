-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_lemma_6_2
-- name    : StrictCQ.CAKKT.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:26.897049+00:00
-- url     : https://prove2.me/theorems/d2196c11-4fdb-4329-8006-2e7d2fcf79fe
-- title:
--   Lemma 6.2, p. 22 — every y ∈ T_Ω(x̄)° is a limit of multiplier combinations with xᵏ → x̄, μᵏ ∝ max{0, g(xᵏ)} and rᵏ → 0
-- statement:
--   Let $h_i,g_j$ be continuously differentiable, $\Omega$ the feasible set, $\bar x\in\Omega$ and $y\in T_\Omega(\bar x)^\circ$. Then there are sequences $x^k\in\mathbb R^n$, $\lambda^k\in\mathbb R^m$, $\mu^k\in\mathbb R^p_+$ and scalars $c_k\ge 0$ such that
--
--   1. $x^k\to\bar x$;
--   2. $\displaystyle \omega^k:=\sum_{i=1}^m\lambda_i^k\nabla h_i(x^k)+\sum_{j=1}^p\mu_j^k\nabla g_j(x^k)\to y$;
--   3. $\mu_j^k=c_k\max\{0,g_j(x^k)\}$ for all $j$ and $k$;
--   4. $\displaystyle r^k:=\sum_{i=1}^m|\lambda_i^kh_i(x^k)|+\sum_{j=1}^p|\mu_j^kg_j(x^k)|\to 0$.
--
--   The lemma approximates a polar tangent vector by multiplier combinations at nearby points with vanishing complementarity residual; it is the bridge from the geometry of $\Omega$ to the sets $K_C(x,r)$ in the proof of Theorem 6.4.
--
--   **Formalization Note** "$\mu_j^k$ is proportional to $\max\{0,g_j(x^k)\}$" is read as one factor $c_k\ge 0$ per $k$, common to all $j$ (the paper's proof has $c_k=k$, and the proof of Theorem 6.4 uses that $\mu_s^k=0$ whenever $g_s(x^k)<0$). The $C^1$ hypothesis is the paper's standing assumption.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 22, Lemma 6.2

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem lemma_6_2 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xbar y : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ C.feasible)
    (hy : y ∈ StrictCQ.AGP.polar (tangentCone C.feasible xbar)) :
    ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ) (c : ℕ → ℝ),
      (∀ k j, 0 ≤ mu k j) ∧ (∀ k, 0 ≤ c k) ∧
      Tendsto x atTop (𝓝 xbar) ∧
      Tendsto (fun k => ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k)) atTop (𝓝 y) ∧
      (∀ k j, mu k j = c k * max 0 (C.g j (x k))) ∧
      Tendsto (fun k => ∑ i, |lam k i * C.h i (x k)| + ∑ j, |mu k j * C.g j (x k)|)
        atTop (𝓝 0) := by sorry
end StrictCQ.CAKKT
