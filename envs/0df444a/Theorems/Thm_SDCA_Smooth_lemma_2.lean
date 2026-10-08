-- Prove2me | Theorems.Thm_SDCA_Smooth_lemma_2
-- name    : SDCA.Smooth.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:39.658889+00:00
-- url     : https://prove2.me/theorems/71d40964-3325-4d5a-b668-3b343aa44a06
-- title:
--   Lemma 2 — $D(\alpha)\le P(w^*)\le P(0)\le 1$ and $D(0)\ge0$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$, convex losses $\varphi_1,\dots,\varphi_n$ satisfying the standing assumptions $\varphi_i(a)\ge0$ for all $i,a$ and $\varphi_i(0)\le1$ for all $i$, and $\lambda>0$. Let $w^*$ minimize the primal objective $P$. Then for every $\alpha\in\mathbb R^n$
--   $$D(\alpha)\ \le\ P(w^*)\ \le\ P(0)\ \le\ 1,$$
--   and in addition $D(0)\ge0$.
--
--   The lemma bounds the initial dual sub-optimality of SDCA started at $\alpha^{(0)}=0$ by $1$, which fixes the constant inside the logarithm of the iteration bounds.
--
--   **Formalization Note** $D(\alpha)$ is `EReal`-valued and is compared with the coerced real $P(w^*)$. The standing assumption $\|x_i\|\le1$ is not needed and not assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, p. 13, Lemma 2 (standing assumptions 2–3, p. 5)

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

namespace SDCA.Smooth

/-- Lemma 2, p. 13 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2): under the standing assumptions
`φᵢ ≥ 0` and `φᵢ(0) ≤ 1` (p. 5), with `w*` a minimizer of `P`, for every `α`
`D(α) ≤ P(w*) ≤ P(0) ≤ 1`, and moreover `D(0) ≥ 0`. -/
theorem lemma_2 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (wstar : EuclideanSpace ℝ (Fin d)) (hwstar : ∀ w, primal lam x φ wstar ≤ primal lam x φ w) :
    (∀ α : Fin n → ℝ, dual lam x φ α ≤ ((primal lam x φ wstar : ℝ) : EReal)) ∧
    primal lam x φ wstar ≤ primal lam x φ 0 ∧ primal lam x φ 0 ≤ 1 ∧
    0 ≤ dual lam x φ 0 := by sorry

end SDCA.Smooth
