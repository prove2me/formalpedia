-- Prove2me | Theorems.Thm_SDCA_Lipschitz_lemma_2
-- name    : SDCA.Lipschitz.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:57.179597+00:00
-- url     : https://prove2.me/theorems/6f7a4dfc-3505-41f4-9f7f-b8d5e9b94237
-- title:
--   Lemma 2, p. 13 — $D(\alpha)\le P(w^*)\le P(0)\le1$ for all $\alpha$, and $D(0)\ge0$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Assume $\phi_i(a)\ge0$ for all $i$ and $a$, and $\phi_i(0)\le1$ for all $i$, and let $w^*$ minimize $P$. Then
--   $$D(\alpha)\le P(w^*)\le P(0)\le1\quad\text{for all }\alpha\in\mathbb R^n,\qquad\text{and}\qquad D(0)\ge0 .$$
--
--   The lemma bounds the initial dual sub-optimality of SDCA started at $\alpha^{(0)}=0$ by $1$, which fixes the burn-in length in Theorem 1.
--
--   **Formalization Note** $D$ takes values in $[-\infty,\infty)$ and the inequalities are in `EReal`. The standing assumption $\|x_i\|\le1$ is not used and not assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, p. 13, Lemma 2

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

namespace SDCA.Lipschitz

/-- Lemma 2, p. 13: if `φᵢ ≥ 0` and `φᵢ(0) ≤ 1` for all `i` and `w*` minimizes `P`, then
for all `α`, `D(α) ≤ P(w*) ≤ P(0) ≤ 1`; in addition, `D(0) ≥ 0`. -/
theorem lemma_2 {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hnonneg : ∀ i a, 0 ≤ φ i a) (hle1 : ∀ i, φ i 0 ≤ 1)
    (wstar : EuclideanSpace ℝ (Fin d)) (hwstar : ∀ w, primal φ x lam wstar ≤ primal φ x lam w) :
    (∀ α : Fin n → ℝ, dual φ x lam α ≤ ((primal φ x lam wstar : ℝ) : EReal)) ∧
      primal φ x lam wstar ≤ primal φ x lam 0 ∧ primal φ x lam 0 ≤ 1 ∧
      0 ≤ dual φ x lam 0 := by sorry

end SDCA.Lipschitz
