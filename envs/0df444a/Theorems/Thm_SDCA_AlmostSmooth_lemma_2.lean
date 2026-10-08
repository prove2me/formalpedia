-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_lemma_2
-- name    : SDCA.AlmostSmooth.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:26.070923+00:00
-- url     : https://prove2.me/theorems/e72880a9-a274-43ff-bc4c-a90663be74df
-- title:
--   Lemma 2 — $D(\alpha)\le P(w^*)\le P(0)\le 1$ for all $\alpha$, and $D(0)\ge0$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$, $\lambda>0$, and losses $\varphi_i:\mathbb R\to\mathbb R$ with $\varphi_i(a)\ge0$ for all $a$ and $\varphi_i(0)\le1$. Let $w^*$ minimize the primal objective $P$ of (1). Then for every dual variable $\alpha\in\mathbb R^n$,
--   $$
--   D(\alpha)\le P(w^*)\le P(0)\le1,
--   $$
--   and in addition $D(0)\ge0$.
--
--   The first inequality is weak duality. Together with $D(0)\ge0$ it bounds the initial dual sub-optimality of SDCA started at $\alpha^{(0)}=0$ by $1$.
--
--   **Formalization Note** $D(\alpha)$ is compared with $P(w^*)$ in `EReal`, so the statement covers infeasible $\alpha$, where $D(\alpha)=-\infty$. Only the standing assumptions 2–3 of p. 5 are used; the assumption $\|x_i\|\le1$ and convexity of the losses are not needed and not assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 13, Lemma 2

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model

namespace SDCA.AlmostSmooth

/-- Lemma 2 (p. 13): under the standing assumptions `φᵢ ≥ 0` and `φᵢ(0) ≤ 1`, with `w*` a
minimizer of `P`: for all `α`, `D(α) ≤ P(w*) ≤ P(0) ≤ 1`; in addition `D(0) ≥ 0`. -/
theorem lemma_2 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1) (lam : ℝ)
    (hlam : 0 < lam) (wstar : EuclideanSpace ℝ (Fin d))
    (hwstar : ∀ w, SDCA.Smooth.primal lam x φ wstar ≤ SDCA.Smooth.primal lam x φ w) :
    (∀ α : Fin n → ℝ, SDCA.Smooth.dual lam x φ α ≤ (SDCA.Smooth.primal lam x φ wstar : EReal)) ∧
      SDCA.Smooth.primal lam x φ wstar ≤ SDCA.Smooth.primal lam x φ 0 ∧ SDCA.Smooth.primal lam x φ 0 ≤ 1 ∧
      0 ≤ SDCA.Smooth.dual lam x φ 0 := by sorry

end SDCA.AlmostSmooth
