-- Prove2me | Theorems.Thm_TsallisINF_StoAlpha_lemma_17
-- name    : TsallisINF.StoAlpha.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:39:44.527984+00:00
-- url     : https://prove2.me/theorems/cbb901bd-036b-41c8-81e8-d77c2d3baf59
-- title:
--   Lemma 17, p. 34 — one mirror step against losses ≥ −1 at most doubles $w_i^{2-\alpha}$ when $\eta_t\xi_i\le 1/4$
-- statement:
--   Let $K\ge1$, $\alpha\in(0,1)$, $\eta>0$ and $\xi\in\mathbb R^K$ with $\xi_i>0$ and $\eta\xi_i\le\frac14$ for all $i$. Let $w$ be a point of the probability simplex $\Delta^{K-1}$ with all coordinates positive, let $\ell\in\mathbb R^K$ with $\ell_i\ge-1$ for all $i$, and set
--   $$\tilde w=\nabla\Psi_t^*\big(\nabla\Psi_t(w)-\ell\big),$$
--   where $\nabla\Psi_t(w)_i=-\frac{w_i^{\alpha-1}-1}{(1-\alpha)\eta\xi_i}$ and $\nabla\Psi_t^*(Y)_i=\big(-\eta(1-\alpha)\xi_iY_i+1\big)^{1/(\alpha-1)}$; explicitly $\tilde w_i=\big(w_i^{\alpha-1}+\eta(1-\alpha)\xi_i\ell_i\big)^{1/(\alpha-1)}$. Then
--   $$\tilde w_i^{\,2-\alpha}\le 2\,w_i^{\,2-\alpha}\qquad\text{for all } i.$$
--
--   The lemma controls the Hessian of $\Psi_t^*$ along a mirror step with slightly negative losses; it is what makes the fourth bound of Lemma 11 possible.
--
--   **Formalization Note** The coordinates of $w$ are assumed positive, because $\nabla\Psi_t(w)$ is only defined there. The base $w_i^{\alpha-1}+\eta(1-\alpha)\xi_i\ell_i$ is then at least $3/4$, so the real power is well defined. The page states the lemma for $\alpha\in[0,1]$ (with $\Psi$ at $\alpha\in\{0,1\}$ given by limits); the Lean statement takes $\alpha\in(0,1)$.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, p. 34, Lemma 17 (with the gradient formulas and (9) on p. 34)

import Mathlib
import Definitions.Def_TsallisINF_StoAlpha_Setting

open MeasureTheory

namespace TsallisINF.StoAlpha
theorem lemma_17 {K : ℕ} (hK : 0 < K) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ξ : Fin K → ℝ)
    (hξ : ∀ i, 0 < ξ i) (η : ℝ) (hη : 0 < η) (hηξ : ∀ i, η * ξ i ≤ 1 / 4)
    (w : Fin K → ℝ) (hw : w ∈ stdSimplex ℝ (Fin K)) (hwpos : ∀ i, 0 < w i)
    (ℓ : Fin K → ℝ) (hℓ : ∀ i, -1 ≤ ℓ i) :
    ∀ i, gradPsiConj α ξ η (fun k => gradPsi α ξ η w k - ℓ k) i ^ (2 - α) ≤
      2 * w i ^ (2 - α) := by sorry
end TsallisINF.StoAlpha
