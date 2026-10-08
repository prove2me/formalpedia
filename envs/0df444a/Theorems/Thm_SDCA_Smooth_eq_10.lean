-- Prove2me | Theorems.Thm_SDCA_Smooth_eq_10
-- name    : SDCA.Smooth.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:18.830988+00:00
-- url     : https://prove2.me/theorems/758ae87a-449d-4996-9fe4-0a88af229a2f
-- title:
--   Eq. (10): the one-coordinate dual increase of an SDCA step
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$, convex losses $\varphi_1,\dots,\varphi_n$, and $\lambda>0$. Let $\Delta$ be an SDCA step (for every dual point and coordinate it maximizes the coordinate objective). Fix a dual point $\alpha$ and a coordinate $i$ with $\varphi_i^*(-\alpha_i)<+\infty$, put $w=w(\alpha)$, and let
--   $$A=\max_{\delta}\Big[-\varphi_i^*\big(-(\alpha_i+\delta)\big)-\tfrac{\lambda n}{2}\big\|w+(\lambda n)^{-1}\delta x_i\big\|^2\Big],\qquad B=-\varphi_i^*(-\alpha_i)-\tfrac{\lambda n}{2}\|w\|^2,$$
--   so that $A$ is the value at $\delta=\Delta(\alpha,i)$ and $B$ the value at $\delta=0$. Assume $\varphi_i^*$ is $\gamma$-strongly convex for some $\gamma\ge0$, and let $u\in\mathbb R$ satisfy $-u\in\partial\varphi_i(w^\top x_i)$. Then for every $s\in[0,1]$
--   $$A-B\ \ge\ s\Big(\varphi_i(w^\top x_i)+\varphi_i^*(-\alpha_i)+\alpha_i\,w^\top x_i+\Big(\frac{\gamma(1-s)}{2}-\frac{s\|x_i\|^2}{2\lambda n}\Big)(u-\alpha_i)^2\Big).$$
--
--   Since $n\,[D(\alpha+\Delta(\alpha,i)e_i)-D(\alpha)]=A-B$, this is the per-coordinate dual improvement estimate from which Lemma 1 follows by averaging over $i$.
--
--   **Formalization Note** The inequality is in `EReal` (with the feasibility hypothesis all terms are finite). $-u\in\partial\varphi_i(a)$ is the subgradient inequality $\varphi_i(a)+(-u)(z-a)\le\varphi_i(z)$ for all $z$. Strong convexity of $\varphi_i^*$ is the predicate `ConjStronglyConvex` (the paper's display on p. 2); $\gamma=0$ is allowed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, proof of Lemma 1, pp. 12–13, eq. (10)

import Mathlib
import Definitions.Def_SDCA_Smooth_Model
open scoped InnerProductSpace

namespace SDCA.Smooth

/-- Eq. (10), §7.1, p. 13 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2), for one SDCA step on
coordinate `i` at a dual-feasible point `α` (`φᵢ*(−αᵢ) < ∞`), with `w = w(α)`. Let
`A = max_δ [−φᵢ*(−(αᵢ + δ)) − (λn/2)‖w + (λn)⁻¹ δ xᵢ‖²]` (attained at the SDCA step `Δ α i`) and
`B = −φᵢ*(−αᵢ) − (λn/2)‖w‖²` (its value at `δ = 0`). If `φᵢ*` is `γ`-strongly convex (`γ ≥ 0`) and
`−u ∈ ∂φᵢ(wᵀxᵢ)`, then for every `s ∈ [0, 1]`
`A − B ≥ s (φᵢ(wᵀxᵢ) + φᵢ*(−αᵢ) + αᵢ wᵀxᵢ + (γ(1 − s)/2 − s‖xᵢ‖²/(2λn)) (u − αᵢ)²)`. -/
theorem eq_10 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (i : Fin n) (hfeas : SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤)
    (γ : ℝ) (hγ : 0 ≤ γ) (hsc : ConjStronglyConvex (φ i) γ)
    (u : ℝ)
    (hu : ∀ z : ℝ, φ i ⟪wOf lam x α, x i⟫_ℝ + (-u) * (z - ⟪wOf lam x α, x i⟫_ℝ) ≤ φ i z)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    coordObj lam x φ α i (Δ α i) - coordObj lam x φ α i 0 ≥
      ((s : ℝ) : EReal) *
        (((φ i ⟪wOf lam x α, x i⟫_ℝ : ℝ) : EReal) + SDCA.Lipschitz.conj (φ i) (-α i) +
          ((α i * ⟪wOf lam x α, x i⟫_ℝ +
              (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)) := by sorry

end SDCA.Smooth
