-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_Supplement_theorem_3
-- name    : SpatialDemandEq.Optimal.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:39:27.140156+00:00
-- url     : https://prove2.me/theorems/d0b79ce8-d512-409f-a1c8-37e443a05688
-- title:
--   Theorem 3, p. 11 — ∂w*_j/∂λ ≥ 0, ∂w*_j/∂μ_k ≤ 0, and ∂w*_k/∂μ_k < ∂w*_j/∂μ_k for j ≠ k
-- statement:
--   Work in the spatial service model (region $\mathcal S$, normalized demand $\nu$ held fixed, distances $d_k$, constants $c > 0$, $\lambda > 0$, under the standing assumptions), with service rates $\mu \in \mathbb R^K$. Let $w^*$ denote the solution of the equilibrium condition (3), $w^*_k = c/(\mu_k - \lambda A_k(w^*))$ with $\lambda A_k(w^*) < \mu_k$, viewed as a function of the parameter that varies. Then:
--
--   1. **Arrival rate.** If $\lambda' \mapsto w^*(\lambda')$ solves (3) with arrival rate $\lambda'$ for every $\lambda'$ near $\lambda$, is differentiable at $\lambda$, and every area map is differentiable at $w^*(\lambda)$, then
--   $$\frac{\partial w^*_j}{\partial \lambda} \ge 0 \qquad\text{for all } j.$$
--   2. **Service rates.** Fix $k$. If $t \mapsto w^*(t)$ solves (3) with $\mu_k$ replaced by $t$ (the other rates unchanged) for every $t$ near $\mu_k$, is differentiable at $\mu_k$, and every area map is differentiable at $w^*(\mu_k)$, then
--   $$\frac{\partial w^*_j}{\partial \mu_k} \le 0 \quad\text{for all } j, \qquad \frac{\partial w^*_k}{\partial \mu_k} < \frac{\partial w^*_j}{\partial \mu_k}\quad\text{for all } j \ne k .$$
--
--   Since the weights are the scaled expected waiting times, a higher arrival rate raises every waiting time, and adding capacity at any facility lowers all of them, the most at that facility itself.
--
--   **Formalization Note** By Theorem 2 (published), solutions of (3) are unique, so any such family is the solution map $w^*$ of the paper. The capacity conditions $\mu_k > 0$ and $\sum_k \mu_k > \lambda$ are not separate hypotheses: they follow from the stability conjuncts $\lambda A_k(w^*) < \mu_k$ of (3) and $\sum_k A_k = 1$.
--
--   Differences from the source:
--   - reading: "Let w* be the unique solution of (3)" and its derivatives ∂w*/∂λ, ∂w*/∂μ_k, presupposed to exist → any family solving (3) for all parameter values in a neighbourhood, with derivative w' at the parameter (`HasDerivAt`), and every area map w ↦ A_j(w) differentiable at w*; reason: the paper differentiates w* and A_j throughout §3.3 without stating regularity; by Theorem 2 the family is the solution map
--   - reading: ∂w*_k/∂μ_k < ∂w*_j/∂μ_k → for every j ≠ k; reason: the proof (p. 12) compares (I − D)^{-1}_kk with (I − D)^{-1}_jk for j ≠ k; for j = k the strict inequality is false
--   - reading: the variation in λ keeps m(x) fixed; the variation in μ_k changes only μ_k → ν, S, the facilities and μ fixed while λ varies; `Function.update μ k t` while μ_k varies; reason: §3.3, p. 10, "we fix the normalized arrival intensity function m(x)"
--   - encoding: the standing assumptions of §3.1 → the published `Standing` of the base mission; reason: inherited base conventions, disclosed on the published definition
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 11, Theorem 3 (§3.3, pp. 10–12)

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory SpatialDemandEq.Optimal

namespace SpatialDemandEq.Optimal.Supplement

theorem theorem_3 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ) :
    (∀ (wl : ℝ → Fin K → ℝ) (wl' : Fin K → ℝ),
        (∀ᶠ l in nhds lam, IsEqWeight ν S (distFn dst xs) c l μ (wl l)) →
        HasDerivAt wl wl' lam →
        (∀ j, DifferentiableAt ℝ
          (fun w : Fin K → ℝ => area ν (cell S (distFn dst xs) w j)) (wl lam)) →
        ∀ j, 0 ≤ wl' j) ∧
    (∀ (k : Fin K) (wm : ℝ → Fin K → ℝ) (wm' : Fin K → ℝ),
        (∀ᶠ t in nhds (μ k),
          IsEqWeight ν S (distFn dst xs) c lam (Function.update μ k t) (wm t)) →
        HasDerivAt wm wm' (μ k) →
        (∀ j, DifferentiableAt ℝ
          (fun w : Fin K → ℝ => area ν (cell S (distFn dst xs) w j)) (wm (μ k))) →
        (∀ j, wm' j ≤ 0) ∧ ∀ j, j ≠ k → wm' k < wm' j) := by sorry

end SpatialDemandEq.Optimal.Supplement
