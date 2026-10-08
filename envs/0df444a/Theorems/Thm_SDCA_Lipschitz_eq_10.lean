-- Prove2me | Theorems.Thm_SDCA_Lipschitz_eq_10
-- name    : SDCA.Lipschitz.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:00.471116+00:00
-- url     : https://prove2.me/theorems/9058506f-935c-4437-a8a3-12e018c31bb0
-- title:
--   (10), p. 13 — one SDCA coordinate step increases $n\,D$ by at least $s(\phi(w^\top x)+\phi^*(-\alpha)+\alpha w^\top x+(\tfrac{\gamma(1-s)}2-\tfrac{s\|x\|^2}{2\lambda n})(u-\alpha)^2)$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Let $\alpha\in\mathbb R^n$ be dual feasible, i.e. $\phi_j^*(-\alpha_j)<\infty$ for every $j$, let $w=w(\alpha)$, and fix a coordinate $i$. Let $\gamma\ge0$ and assume $\phi_i^*$ is $\gamma$-strongly convex: for all $u,v\in\mathbb R$ and $r\in[0,1]$,
--   $$\phi_i^*(ru+(1-r)v)\le r\phi_i^*(u)+(1-r)\phi_i^*(v)-\frac\gamma2r(1-r)(u-v)^2 .$$
--   Let $-u\in\partial\phi_i(w^\top x_i)$ and $s\in[0,1]$. Let $A$ be the maximal value of the coordinate objective $\delta\mapsto-\phi_i^*(-(\alpha_i+\delta))-\frac{\lambda n}2\|w+(\lambda n)^{-1}\delta x_i\|^2$ (attained at the SDCA step $\Delta(\alpha,i)$) and $B$ its value at $\delta=0$. Then
--   $$A-B\ \ge\ s\Bigl(\phi_i(w^\top x_i)+\phi_i^*(-\alpha_i)+\alpha_iw^\top x_i+\Bigl(\frac{\gamma(1-s)}2-\frac{s\|x_i\|^2}{2\lambda n}\Bigr)(u-\alpha_i)^2\Bigr).$$
--
--   Since $A-B=n\,[D(\alpha+\Delta(\alpha,i)e_i)-D(\alpha)]$, this bounds the dual increase of one SDCA iteration that picks coordinate $i$; averaged over $i$ it yields Lemma 1.
--
--   **Formalization Note** The inequality is in `EReal`; $B$ and $\phi_i^*(-\alpha_i)$ are finite by dual feasibility. The strong-convexity hypothesis is the p. 2 display, written in `EReal` with the convention $0\cdot\infty=0$. The step is any map satisfying the arg-max predicate `IsSDCAStep`.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, proof of Lemma 1, p. 13, (10) (with (8) and (9), pp. 12–13)

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

namespace SDCA.Lipschitz

/-- (10), §7.1, p. 13: one-coordinate increase of an SDCA step. Let `α` be a dual-feasible state
(`φⱼ*(−αⱼ) < ∞` for every `j`), `i` a coordinate, `w = w(α)`, `s ∈ [0, 1]`, `γ ≥ 0` with `φᵢ*`
`γ`-strongly convex (p. 2 display), and `−u ∈ ∂φᵢ(wᵀxᵢ)`. With `A` the maximized coordinate
objective (at `Δαᵢ = Δ α i`) and `B` its value at `Δαᵢ = 0`,
`A − B ≥ s (φᵢ(wᵀxᵢ) + φᵢ*(−αᵢ) + αᵢwᵀxᵢ + (γ(1−s)/2 − s‖xᵢ‖²/(2λn)) (u − αᵢ)²)`. -/
theorem eq_10 {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (α : Fin n → ℝ) (hα : ∀ j, conj (φ j) (-α j) ≠ ⊤) (i : Fin n)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hsc : ∀ (u v r : ℝ), 0 ≤ r → r ≤ 1 →
      conj (φ i) (r * u + (1 - r) * v) ≤
        ((r : ℝ) : EReal) * conj (φ i) u + ((1 - r : ℝ) : EReal) * conj (φ i) v
          - ((γ * r * (1 - r) / 2 * (u - v) ^ 2 : ℝ) : EReal))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (u : ℝ) (hu : -u ∈ subdiff (φ i) (inner ℝ (wOf x lam α) (x i))) :
    coordObj φ x lam α i (Δ α i) - coordObj φ x lam α i 0 ≥
      ((s : ℝ) : EReal) *
        (((φ i (inner ℝ (wOf x lam α) (x i)) + α i * inner ℝ (wOf x lam α) (x i)
            + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)
          + conj (φ i) (-α i)) := by sorry

end SDCA.Lipschitz
