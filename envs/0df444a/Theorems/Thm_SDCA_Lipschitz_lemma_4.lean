-- Prove2me | Theorems.Thm_SDCA_Lipschitz_lemma_4
-- name    : SDCA.Lipschitz.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:59.330318+00:00
-- url     : https://prove2.me/theorems/dee171ed-5703-47a0-a238-3c67226bd22a
-- title:
--   Lemma 4, p. 15 — for $L$-Lipschitz losses the variance term $G$ of Lemma 1 (with $\gamma=0$) is at most $4L^2$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   Assume $\|x_i\|\le1$ for all $i$, $L>0$, and every $\phi_i$ is $L$-Lipschitz. Let $u_i(\cdot)$ be a sub-gradient selection, $-u_i(a)\in\partial\phi_i(a)$, and let $\alpha$ be dual feasible ($\phi_j^*(-\alpha_j)<\infty$ for all $j$), $w=w(\alpha)$ and $u_i=u_i(x_i^\top w)$. Then the quantity $G$ of Lemma 1 with $\gamma=0$ satisfies
--   $$G=\frac1n\sum_{i=1}^n\|x_i\|^2(u_i-\alpha_i)^2\ \le\ 4L^2 .$$
--
--   It turns Lemma 1 into the recursion (13) with the constant $G\le4L^2$, which drives the rate of Theorem 1.
--
--   **Formalization Note** This is the conditional form at a fixed dual-feasible state (the paper's $G^{(t)}$ averages it over the history). The hypothesis $\|x_i\|\le1$ is the paper's standing assumption 1 (p. 5), which the proof uses.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.2, p. 15, Lemma 4

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

namespace SDCA.Lipschitz

/-- Lemma 4, p. 15, in conditional form: if every `φᵢ` is `L`-Lipschitz and `‖xᵢ‖ ≤ 1`, then for
every dual-feasible state `α` and every sub-gradient selection `u` (`−u i a ∈ ∂φᵢ(a)`), the
quantity `G` of Lemma 1 with `γ = 0`, `(1/n) ∑ᵢ ‖xᵢ‖² (uᵢ − αᵢ)²` with `uᵢ = u i (xᵢᵀw(α))`,
is at most `4L²`. -/
theorem lemma_4 {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hx : ∀ i, ‖x i‖ ≤ 1)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ i (a b : ℝ), |φ i a - φ i b| ≤ L * |a - b|)
    (u : Fin n → ℝ → ℝ) (hu : ∀ i a, -(u i a) ∈ subdiff (φ i) a)
    (α : Fin n → ℝ) (hα : ∀ j, conj (φ j) (-α j) ≠ ⊤) :
    (1 / (n : ℝ)) * ∑ i, ‖x i‖ ^ 2 * (u i (inner ℝ (wOf x lam α) (x i)) - α i) ^ 2
      ≤ 4 * L ^ 2 := by sorry

end SDCA.Lipschitz
