-- Prove2me | Theorems.Thm_SDCA_Lipschitz_averaged_gap_bound
-- name    : SDCA.Lipschitz.averaged_gap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:14.195252+00:00
-- url     : https://prove2.me/theorems/c41c13a2-953b-41c0-8568-3be8f0adcf9e
-- title:
--   §7.2, p. 16 — $\mathbb E[P(\bar w)-D(\bar\alpha)]\le\frac{n}{s(T-T_0)}\mathbb E[D(\alpha^{(T)})-D(\alpha^{(T_0)})]+\frac{sG}{2\lambda n}$ for the averaged output
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Assume $\|x_i\|\le1$ and $\phi_i\ge0$ for all $i$, $L>0$, and every $\phi_i$ is $L$-Lipschitz. Run SDCA from $\alpha^{(0)}=0$ with an SDCA step rule and uniformly random coordinates for $T$ iterations, let $T_0<T$, and let $\bar\alpha=\frac1{T-T_0}\sum_{t=T_0+1}^T\alpha^{(t-1)}$ and $\bar w=w(\bar\alpha)$ (the Averaging option). With $G=4L^2$, for every $0<s\le1$, all dual values involved are finite and
--   $$\mathbb E\bigl[P(\bar w)-D(\bar\alpha)\bigr]\ \le\ \frac{n}{s(T-T_0)}\,\mathbb E\bigl[D(\alpha^{(T)})-D(\alpha^{(T_0)})\bigr]+\frac{sG}{2\lambda n}.$$
--
--   Combined with (14) and the choice $s=n/(T-T_0)$, this gives the duality-gap guarantee of Theorem 1.
--
--   **Formalization Note** Expectations are over the $T$ uniformly random coordinates (`SAGA.Convex.expectIdx`). The paper states the bound for the averaged output or for a random iterate among $t\in\{T_0+1,\dots,T\}$; this item is the averaged output. $G$ is pinned to $4L^2$.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.2, p. 16, second display (after "randomly chosen vector over t ∈ {T0+1, …, T}")

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model
import Definitions.Def_SAGA_Convex_sagaRun

namespace SDCA.Lipschitz

/-- §7.2, p. 16, second display, with `G := 4L²` (Averaging option). SDCA from `α⁽⁰⁾ = 0` with
`L`-Lipschitz losses, `T₀ < T`, `0 < s ≤ 1`, `ᾱ` the average of `α⁽ᵀ⁰⁾, …, α⁽ᵀ⁻¹⁾` and
`w̄ = w(ᾱ)`: `E[P(w̄) − D(ᾱ)] ≤ n/(s(T − T₀)) E[D(α⁽ᵀ⁾) − D(α⁽ᵀ⁰⁾)] + sG/(2λn)`;
all dual values involved are finite. -/
theorem averaged_gap_bound {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hx : ∀ i, ‖x i‖ ≤ 1) (hnonneg : ∀ i a, 0 ≤ φ i a)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ i (a b : ℝ), |φ i a - φ i b| ≤ L * |a - b|)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (T0 T : ℕ) (hT : T0 < T) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∀ js : Fin T → Fin n, dual φ x lam (avgDual Δ 0 js T0) ≠ ⊥ ∧
      dual φ x lam (sdcaIter Δ 0 js T) ≠ ⊥ ∧ dual φ x lam (sdcaIter Δ 0 js T0) ≠ ⊥) ∧
      SAGA.Convex.expectIdx n T
          (fun js => primal φ x lam (wOf x lam (avgDual Δ 0 js T0))
            - (dual φ x lam (avgDual Δ 0 js T0)).toReal)
        ≤ n / (s * ((T : ℝ) - T0)) * SAGA.Convex.expectIdx n T
            (fun js => (dual φ x lam (sdcaIter Δ 0 js T)).toReal
              - (dual φ x lam (sdcaIter Δ 0 js T0)).toReal)
          + s * (4 * L ^ 2) / (2 * lam * n) := by sorry

end SDCA.Lipschitz
