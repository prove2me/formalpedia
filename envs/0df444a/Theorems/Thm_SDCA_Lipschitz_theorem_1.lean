-- Prove2me | Theorems.Thm_SDCA_Lipschitz_theorem_1
-- name    : SDCA.Lipschitz.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:14.779952+00:00
-- url     : https://prove2.me/theorems/cf1091d1-f342-4502-a2a7-3f83cf8b076e
-- title:
--   Theorem 1, p. 5 — SDCA with $L$-Lipschitz losses: $\mathbb E[P(\bar w)-D(\bar\alpha)]\le\epsilon_P$ once $T\ge T_0+n+4L^2/(\lambda\epsilon_P)$ with burn-in $T_0$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$) with $\|x_i\|\le1$, let $\lambda>0$, and let $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ be convex and $L$-Lipschitz ($L>0$) with $\phi_i(a)\ge0$ for all $a$ and $\phi_i(0)\le1$. Let $P$ be the primal objective (1), $D$ the dual objective (2) and $\alpha^*$ a maximizer of $D$.
--
--   Run Procedure SDCA from $\alpha^{(0)}=0$: at each iteration pick a coordinate $i$ uniformly at random (independently of the past) and increase $\alpha_i$ by an increment $\Delta\alpha_i$ that maximizes $-\phi_i^*(-(\alpha_i^{(t-1)}+\Delta\alpha_i))-\frac{\lambda n}2\|w^{(t-1)}+(\lambda n)^{-1}\Delta\alpha_ix_i\|^2$, where $w^{(t)}=w(\alpha^{(t)})$. Let $\epsilon_P>0$ and let $T_0,T$ be integers with
--   $$T\ \ge\ T_0+n+\frac{4L^2}{\lambda\epsilon_P}\ \ge\ \max\bigl(0,\lceil n\log(0.5\lambda nL^{-2})\rceil\bigr)+n+\frac{20L^2}{\lambda\epsilon_P}.$$
--   Let $\bar\alpha=\frac1{T-T_0}\sum_{t=T_0+1}^T\alpha^{(t-1)}$ and $\bar w=w(\bar\alpha)$ (Averaging option). Then:
--
--   1. all dual values $D(\alpha^*)$, $D(\alpha^{(t)})$ ($t\le T$) and $D(\bar\alpha)$ are finite;
--   2. the expected duality gap satisfies $$\mathbb E\bigl[P(\bar w)-D(\bar\alpha)\bigr]\le\epsilon_P ;$$
--   3. moreover, for every $t\ge T_0$, $\;\mathbb E\bigl[D(\alpha^*)-D(\alpha^{(t)})\bigr]\le\epsilon_P/2$.
--
--   This is the convergence guarantee of SDCA for Lipschitz losses such as the hinge loss of the SVM: $\tilde O(n+L^2/(\lambda\epsilon_P))$ iterations suffice for a duality gap $\epsilon_P$, which also bounds the primal sub-optimality.
--
--   **Formalization Note** The two printed inequalities are kept as two hypotheses on $(T,T_0)$. $\max(0,\lceil\cdot\rceil)$ is an integer ceiling inside an integer maximum. The step is any map satisfying the arg-max predicate `IsSDCAStep`; the conjugate and $D$ are `EReal`-valued and are converted to reals only under the finiteness asserted in item 1. Expectations are uniform averages over coordinate sequences (`SAGA.Convex.expectIdx`); in item 3 the run has length $t$.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §3, p. 5, Theorem 1 (with Procedure SDCA, Averaging option, and standing assumptions 1–3, p. 5)

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model
import Definitions.Def_SAGA_Convex_sagaRun

namespace SDCA.Lipschitz

/-- Theorem 1, p. 5. Procedure SDCA with `α⁽⁰⁾ = 0`, coordinates picked i.i.d. uniformly, under the
standing assumptions `‖xᵢ‖ ≤ 1`, `φᵢ ≥ 0`, `φᵢ(0) ≤ 1`, with convex `L`-Lipschitz `φᵢ`. If
`T ≥ T₀ + n + 4L²/(λϵ_P) ≥ max(0, ⌈n log(0.5λnL⁻²)⌉) + n + 20L²/(λϵ_P)`, then the Averaging-option
output (`ᾱ` = average of `α⁽ᵀ⁰⁾, …, α⁽ᵀ⁻¹⁾`, `w̄ = w(ᾱ)`) has expected duality gap
`E[P(w̄) − D(ᾱ)] ≤ ϵ_P`, and for every `t ≥ T₀`, `E[D(α*) − D(α⁽ᵗ⁾)] ≤ ϵ_P/2`. All dual values
involved are finite. -/
theorem theorem_1 {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hx : ∀ i, ‖x i‖ ≤ 1) (hnonneg : ∀ i a, 0 ≤ φ i a) (hle1 : ∀ i, φ i 0 ≤ 1)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ i (a b : ℝ), |φ i a - φ i b| ≤ L * |a - b|)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (αstar : Fin n → ℝ) (hαstar : ∀ β, dual φ x lam β ≤ dual φ x lam αstar)
    (εP : ℝ) (hε : 0 < εP) (T0 T : ℕ)
    (hT : (T : ℝ) ≥ T0 + n + 4 * L ^ 2 / (lam * εP))
    (hT0 : (T0 : ℝ) + n + 4 * L ^ 2 / (lam * εP) ≥
      (((max 0 ⌈(n : ℝ) * Real.log (0.5 * lam * n / L ^ 2)⌉ : ℤ)) : ℝ) + n
        + 20 * L ^ 2 / (lam * εP)) :
    (dual φ x lam αstar ≠ ⊥ ∧
      ∀ js : Fin T → Fin n, (∀ t ≤ T, dual φ x lam (sdcaIter Δ 0 js t) ≠ ⊥) ∧
        dual φ x lam (avgDual Δ 0 js T0) ≠ ⊥) ∧
    SAGA.Convex.expectIdx n T
        (fun js => primal φ x lam (wOf x lam (avgDual Δ 0 js T0))
          - (dual φ x lam (avgDual Δ 0 js T0)).toReal) ≤ εP ∧
    ∀ t : ℕ, T0 ≤ t →
      (∀ js : Fin t → Fin n, dual φ x lam (sdcaIter Δ 0 js t) ≠ ⊥) ∧
      SAGA.Convex.expectIdx n t
          (fun js => (dual φ x lam αstar).toReal - (dual φ x lam (sdcaIter Δ 0 js t)).toReal)
        ≤ εP / 2 := by sorry

end SDCA.Lipschitz
