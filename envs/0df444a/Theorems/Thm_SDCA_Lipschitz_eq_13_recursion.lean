-- Prove2me | Theorems.Thm_SDCA_Lipschitz_eq_13_recursion
-- name    : SDCA.Lipschitz.eq_13_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:49.515484+00:00
-- url     : https://prove2.me/theorems/d8bbdbf3-8192-4721-b893-0659678988af
-- title:
--   (13) and the recursion after it, p. 15 — $\mathbb E[\epsilon_D^{(t)}]\le(1-\frac sn)\mathbb E[\epsilon_D^{(t-1)}]+(\frac sn)^2\frac{G}{2\lambda}$ with $G=4L^2$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Assume $\|x_i\|\le1$ and $\phi_i\ge0$ for all $i$, $L>0$, and every $\phi_i$ is $L$-Lipschitz. Run SDCA from $\alpha^{(0)}=0$ with an SDCA step rule, picking at each iteration a coordinate uniformly at random, independently. Let $\alpha^*$ maximize $D$ and $\epsilon_D^{(t)}=D(\alpha^*)-D(\alpha^{(t)})$. With $G=4L^2$, for every $t\ge0$ and every $0<s\le1$, all dual values involved are finite and
--   $$\mathbb E\bigl[\epsilon_D^{(t+1)}\bigr]\ \le\ \Bigl(1-\frac sn\Bigr)\mathbb E\bigl[\epsilon_D^{(t)}\bigr]+\Bigl(\frac sn\Bigr)^2\frac{G}{2\lambda}.$$
--
--   This recursion for the dual sub-optimality is solved in (14).
--
--   **Formalization Note** The expectation of a quantity depending on the first $t$ coordinates is the uniform average over $\{1,\dots,n\}^t$ (`SAGA.Convex.expectIdx`). The paper takes $G=\max_tG^{(t)}$; since (13) remains true with any upper bound, $G$ is pinned to the bound $4L^2$ of Lemma 4, which is the value the burn-in of Theorem 1 is computed with. The step $t-1\to t$ is written $t\to t+1$. $\phi_i\ge0$ (standing assumption 2) makes $\alpha^{(0)}=0$ dual feasible.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.2, p. 15, (13) and the display after it

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model
import Definitions.Def_SAGA_Convex_sagaRun

namespace SDCA.Lipschitz

/-- (13) and the recursion after it, §7.2, p. 15, with `G := 4L²`. SDCA from `α⁽⁰⁾ = 0` with
`L`-Lipschitz losses, coordinates picked i.i.d. uniformly. For `ϵ_D⁽ᵗ⁾ = D(α*) − D(α⁽ᵗ⁾)`, every
`t ≥ 0` and every `0 < s ≤ 1`,
`E[ϵ_D⁽ᵗ⁺¹⁾] ≤ (1 − s/n) E[ϵ_D⁽ᵗ⁾] + (s/n)² G/(2λ)`; all dual values involved are finite. -/
theorem eq_13_recursion {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hx : ∀ i, ‖x i‖ ≤ 1) (hnonneg : ∀ i a, 0 ≤ φ i a)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ i (a b : ℝ), |φ i a - φ i b| ≤ L * |a - b|)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (αstar : Fin n → ℝ) (hαstar : ∀ β, dual φ x lam β ≤ dual φ x lam αstar)
    (t : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    dual φ x lam αstar ≠ ⊥ ∧
      (∀ js : Fin t → Fin n, dual φ x lam (sdcaIter Δ 0 js t) ≠ ⊥) ∧
      (∀ js : Fin (t + 1) → Fin n, dual φ x lam (sdcaIter Δ 0 js (t + 1)) ≠ ⊥) ∧
      SAGA.Convex.expectIdx n (t + 1)
          (fun js => (dual φ x lam αstar).toReal - (dual φ x lam (sdcaIter Δ 0 js (t + 1))).toReal)
        ≤ (1 - s / n) * SAGA.Convex.expectIdx n t
            (fun js => (dual φ x lam αstar).toReal - (dual φ x lam (sdcaIter Δ 0 js t)).toReal)
          + (s / n) ^ 2 * (4 * L ^ 2) / (2 * lam) := by sorry

end SDCA.Lipschitz
