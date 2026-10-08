-- Prove2me | Theorems.Thm_SDCA_Lipschitz_eq_14
-- name    : SDCA.Lipschitz.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:14.022211+00:00
-- url     : https://prove2.me/theorems/5ae58019-fa8b-475f-890c-6a7f072ce3da
-- title:
--   (14), p. 15 — $\mathbb E[\epsilon_D^{(t)}]\le\frac{2G}{\lambda(2n+t-t_0)}$ for $t\ge t_0=\max(0,\lceil n\log(2\lambda n\epsilon_D^{(0)}/G)\rceil)$, $G=4L^2$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Assume $\|x_i\|\le1$ and $\phi_i\ge0$ for all $i$, $L>0$, and every $\phi_i$ is $L$-Lipschitz. Run SDCA from $\alpha^{(0)}=0$ with an SDCA step rule and uniformly random coordinates. Let $\alpha^*$ maximize $D$, $\epsilon_D^{(t)}=D(\alpha^*)-D(\alpha^{(t)})$, $G=4L^2$ and
--   $$t_0=\max\Bigl(0,\Bigl\lceil n\log\frac{2\lambda n\,\epsilon_D^{(0)}}{G}\Bigr\rceil\Bigr).$$
--   Then all dual values involved are finite and, for every $t\ge t_0$,
--   $$\mathbb E\bigl[\epsilon_D^{(t)}\bigr]\ \le\ \frac{2G}{\lambda(2n+t-t_0)} .$$
--
--   This is the dual sub-optimality rate of SDCA for Lipschitz losses; it gives the "moreover" part of Theorem 1 and the bound on $\mathbb E[\epsilon_D^{(T_0)}]$ used for the duality gap.
--
--   **Formalization Note** $\epsilon_D^{(0)}=D(\alpha^*)-D(0)$ is deterministic. $\max(0,\lceil\cdot\rceil)$ is written `Nat.ceil`, which equals it. If $\epsilon_D^{(0)}=0$, Lean's convention $\log0=0$ gives $t_0=0$, and the claim is still the paper's. $G$ is pinned to $4L^2$ (see (13)).
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.2, p. 15, (14)

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model
import Definitions.Def_SAGA_Convex_sagaRun

namespace SDCA.Lipschitz

/-- (14), §7.2, p. 15, with `G := 4L²`. SDCA from `α⁽⁰⁾ = 0` with `L`-Lipschitz losses. Let
`ϵ_D⁽⁰⁾ = D(α*) − D(0)` and `t₀ = max(0, ⌈n log(2λn ϵ_D⁽⁰⁾/G)⌉)` (written `Nat.ceil`). For every
`t ≥ t₀`, `E[D(α*) − D(α⁽ᵗ⁾)] ≤ 2G/(λ(2n + t − t₀))`; all dual values involved are finite. -/
theorem eq_14 {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hx : ∀ i, ‖x i‖ ≤ 1) (hnonneg : ∀ i a, 0 ≤ φ i a)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ i (a b : ℝ), |φ i a - φ i b| ≤ L * |a - b|)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (αstar : Fin n → ℝ) (hαstar : ∀ β, dual φ x lam β ≤ dual φ x lam αstar)
    (t : ℕ)
    (ht : ⌈(n : ℝ) * Real.log (2 * lam * n * ((dual φ x lam αstar).toReal
        - (dual φ x lam 0).toReal) / (4 * L ^ 2))⌉₊ ≤ t) :
    dual φ x lam αstar ≠ ⊥ ∧ dual φ x lam 0 ≠ ⊥ ∧
      (∀ js : Fin t → Fin n, dual φ x lam (sdcaIter Δ 0 js t) ≠ ⊥) ∧
      SAGA.Convex.expectIdx n t
          (fun js => (dual φ x lam αstar).toReal - (dual φ x lam (sdcaIter Δ 0 js t)).toReal)
        ≤ 2 * (4 * L ^ 2) / (lam * (2 * n + t
            - ⌈(n : ℝ) * Real.log (2 * lam * n * ((dual φ x lam αstar).toReal
                - (dual φ x lam 0).toReal) / (4 * L ^ 2))⌉₊)) := by sorry

end SDCA.Lipschitz
