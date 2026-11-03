-- Prove2me | Theorems.Thm_TrustIPM_lemma_8
-- name    : TrustIPM.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:20.193193+00:00
-- url     : https://prove2.me/theorems/ba691570-642a-420e-ba3e-98108cbe10ad
-- title:
--   Lemma 8 — optimality conditions and value function of the trust-region subproblem (corrected: converse needs $\|u^*\|\le r$)
-- statement:
--   Let $g\in\mathbb R^n$, $H$ a symmetric $n\times n$ matrix, $\Delta(u):=\tfrac12u^THu+g^Tu$ and $\sigma(r):=\min_{u\in B_r(0)}\Delta(u)$.
--
--   1. If $u^*\in\operatorname{argmin}_{u\in B_r(0)}\Delta(u)$ for some $r\ge0$, there is $\delta\ge0$ with
--   $$\delta(\|u^*\|_2-r)=0,\qquad(H+\delta I)u^*=-g,\qquad H+\delta I\succeq0 .\tag{17}$$
--   2. Conversely, if $\|u^*\|_2\le r$ and $u^*$ satisfies (17) for some $\delta\ge0$, then $u^*\in\operatorname{argmin}_{u\in B_r(0)}\Delta(u)$.
--   3. If $\delta\ge0$ satisfies (17) together with some $u^*$, $\|u^*\|_2\le r$, then $\sigma(r)\le-\delta r^2/2$. (18a)
--   4. For all $r\ge0$ and $\alpha\in[0,1]$, $\sigma(r)\le\sigma(\alpha r)\le\alpha^2\sigma(r)$. (18b)
--   5. $\sigma$ is non-increasing on $[0,\infty)$.
--   6. $\sigma$ is continuous on $[0,\infty)$.
--
--   These are the standard facts about trust-region subproblems that Lemma 9, Lemma 10 and Lemma 11 use.
--
--   **Formalization Note** $H$ is a self-adjoint linear map of `EuclideanSpace ℝ (Fin n)` and $M\succeq0$ means $\langle Mv,v\rangle\ge0$ for every $v$.
--
--   Differences from the source:
--   - encoding: symmetric matrix H ∈ ℝ^{m×n} → self-adjoint H : ℝⁿ → ℝⁿ; reason: a symmetric matrix is square and Hu* must lie in ℝⁿ; m×n is a typo
--   - correction: if u* satisfies (17) then u* ∈ argmin_{u∈B_r(0)} Δ(u) → the converse also assumes ‖u*‖₂ ≤ r; reason: (17) does not force feasibility: n = 1, H = 1, g = −10, r = 1, u* = 10, δ = 0 satisfies (17) but u* ∉ B₁(0)
--   - reading: σ(r) ≤ −δ(r)r²/2 with δ(r) the multiplier of (17) → for every δ ≥ 0 satisfying (17) with some u*, ‖u*‖₂ ≤ r; reason: this covers the paper's δ(r), whichever minimizer it comes from
--   - reading: σ is monotone decreasing and continuous → AntitoneOn and ContinuousOn on [0, ∞); reason: σ is defined for r ∈ [0, ∞) and is constant where g = 0 and H ⪰ 0, so decreasing means non-increasing
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 8, p.13

import Mathlib
import Definitions.Def_TrustIPM_trsModel
open scoped InnerProductSpace RealInnerProductSpace

namespace TrustIPM

/-- **Lemma 8** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 8, p.13), corrected converse. Let `g ∈ ℝⁿ`, `H` a
symmetric `n × n` matrix, `Δ(u) := ½uᵀHu + gᵀu`, and `σ(r) := min_{u ∈ B_r(0)} Δ(u)`.
1. If `u* ∈ argmin_{u ∈ B_r(0)} Δ(u)` for some `r ≥ 0`, there is `δ(r) ≥ 0` with
   `δ(r)(‖u*‖₂ − r) = 0`, `(H + δ(r)I)u* = −g` and `H + δ(r)I ⪰ 0` (17).
2. Conversely, if `u*` with `‖u*‖₂ ≤ r` satisfies (17) then `u* ∈ argmin_{u ∈ B_r(0)} Δ(u)`.
3. `σ(r) ≤ −δ(r)r²/2` (18a), for every `δ(r) ≥ 0` satisfying (17) together with some `u*`,
   `‖u*‖₂ ≤ r`.
4. `σ(r) ≤ σ(αr) ≤ α²σ(r)` for all `r ≥ 0` and `α ∈ [0, 1]` (18b).
5. `σ` is monotone decreasing (non-increasing) on `[0, ∞)`.
6. `σ` is continuous on `[0, ∞)`.

**Formalization Note** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` and `H` a self-adjoint continuous linear
map (the page's "`H ∈ ℝ^{m×n}`" is read as square, since `H` is symmetric). `M ⪰ 0` is
`⟪M v, v⟫ ≥ 0` for every `v`. The page states the converse without `‖u*‖₂ ≤ r`, which is false
(`n = 1`, `H = 1`, `g = −10`, `r = 1`, `u* = 10`, `δ = 0`); the hypothesis is added. -/
theorem lemma_8 {n : ℕ} (hn : 0 < n) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ u v, ⟪H u, v⟫_ℝ = ⟪u, H v⟫_ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    (∀ (r : ℝ) (u : EuclideanSpace ℝ (Fin n)), 0 ≤ r → u ∈ Metric.closedBall 0 r →
        IsMinOn (trsModel H g) (Metric.closedBall 0 r) u →
        ∃ δ : ℝ, 0 ≤ δ ∧ δ * (‖u‖ - r) = 0 ∧ H u + δ • u = -g ∧
          ∀ v, 0 ≤ ⟪H v + δ • v, v⟫_ℝ) ∧
    (∀ (r δ : ℝ) (u : EuclideanSpace ℝ (Fin n)), 0 ≤ δ → ‖u‖ ≤ r → δ * (‖u‖ - r) = 0 →
        H u + δ • u = -g → (∀ v, 0 ≤ ⟪H v + δ • v, v⟫_ℝ) →
        u ∈ Metric.closedBall 0 r ∧ IsMinOn (trsModel H g) (Metric.closedBall 0 r) u) ∧
    (∀ (r δ : ℝ) (u : EuclideanSpace ℝ (Fin n)), 0 ≤ δ → ‖u‖ ≤ r → δ * (‖u‖ - r) = 0 →
        H u + δ • u = -g → (∀ v, 0 ≤ ⟪H v + δ • v, v⟫_ℝ) →
        trsValue H g r ≤ -(δ * r ^ 2) / 2) ∧
    (∀ r α : ℝ, 0 ≤ r → 0 ≤ α → α ≤ 1 →
        trsValue H g r ≤ trsValue H g (α * r) ∧ trsValue H g (α * r) ≤ α ^ 2 * trsValue H g r) ∧
    AntitoneOn (trsValue H g) (Set.Ici 0) ∧
    ContinuousOn (trsValue H g) (Set.Ici 0) := by sorry

end TrustIPM
