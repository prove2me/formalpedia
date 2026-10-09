-- Prove2me | Theorems.Thm_PinningSync_Tree_theta_bound
-- name    : PinningSync.Tree.theta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:58.231244+00:00
-- url     : https://prove2.me/theorems/6e2f84b5-075d-4693-85de-23bfa5b53fe7
-- title:
--   §3, display after (3.5), p. 1402 — with KΓ = ΓK and θ = λmax((K+Kᵀ)/2), Assumption 1 gives (x−y)ᵀ(f(x,t)−f(y,t)) ≤ θ(x−y)ᵀΓ(x−y)
-- statement:
--   Let $f:\mathbb R^n\times\mathbb R_+\to\mathbb R^n$ and let $K,\Gamma\in\mathbb R^{n\times n}$ satisfy Assumption 1:
--   $$
--   (x-y)^{\mathsf T}\bigl(f(x,t)-f(y,t)\bigr)\le (x-y)^{\mathsf T}K\Gamma(x-y)\qquad\forall x,y\in\mathbb R^n,\ t\ge0 .
--   $$
--   Suppose that $\Gamma$ is (symmetric) positive definite, that $K$ and $\Gamma$ commute, and let $\theta=\lambda_{\max}\bigl((K+K^{\mathsf T})/2\bigr)$ as in (3.5). Then
--   $$
--   (x-y)^{\mathsf T}\bigl(f(x,t)-f(y,t)\bigr)\le\theta\,(x-y)^{\mathsf T}\Gamma(x-y)\qquad\forall x,y\in\mathbb R^n,\ t\ge 0 .
--   $$
--
--   This is the one-sided Lipschitz bound with the scalar constant $\theta$ that replaces Assumption 1 in every result of §4; it is the first inequality in the derivative estimate (4.10).
--
--   **Formalization Note** The page says "one can choose a large θ such that" the bound holds, right after defining θ by (3.5); the bound is stated here for the θ of (3.5), which is the θ the proof of Theorem 4.5 uses. "Positive definite" is Mathlib's `Matrix.PosDef`, which includes symmetry. The hypothesis $\theta\ge0$ of p. 1402 is not needed and is omitted. For $n=0$ the λ_max hypothesis cannot hold.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1402, (3.5) and the display after it

import Mathlib
import Definitions.Def_PinningSync_Tree_Setting

open Matrix Kronecker Filter Topology

namespace PinningSync.Tree

theorem theta_bound {n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : PinningSync.Strong.Assumption1 f K Γ) (hΓ : Γ.PosDef)
    (hKΓ : K * Γ = Γ * K) (θ : ℝ) (hθ : PinningSync.Strong.IsLamMax ((1 / 2 : ℝ) • (K + Kᵀ)) θ) :
    ∀ t : ℝ, 0 ≤ t → ∀ x y : Fin n → ℝ,
      (x - y) ⬝ᵥ (f x t - f y t) ≤ θ * ((x - y) ⬝ᵥ (Γ *ᵥ (x - y))) := by sorry

end PinningSync.Tree
