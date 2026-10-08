-- Prove2me | Theorems.Thm_SDCA_Smooth_gap_identity
-- name    : SDCA.Smooth.gap_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:45.975354+00:00
-- url     : https://prove2.me/theorems/f5e7680e-3fa8-4c2a-90f9-311dc6f6091e
-- title:
--   Duality-gap identity $P(w(\alpha))-D(\alpha)=\frac1n\sum_i(\varphi_i(w^\top x_i)+\varphi_i^*(-\alpha_i)+\alpha_i w^\top x_i)$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ with $n\ge1$, let $\varphi_1,\dots,\varphi_n:\mathbb R\to\mathbb R$ be convex, let $\lambda>0$, and let $P$ and $D$ be the primal and dual objectives of problems (1) and (2). For every dual point $\alpha\in\mathbb R^n$, with $w=w(\alpha)=\frac{1}{\lambda n}\sum_i\alpha_ix_i$,
--   $$P(w)-D(\alpha)=\frac1n\sum_{i=1}^n\Big(\varphi_i(w^\top x_i)+\varphi_i^*(-\alpha_i)+\alpha_i\,w^\top x_i\Big),$$
--   as an identity in $(-\infty,+\infty]$: both sides are $+\infty$ exactly when some $\varphi_i^*(-\alpha_i)=+\infty$.
--
--   The identity writes the duality gap as an average of nonnegative Fenchel–Young gaps, one per example; taking the expectation of the one-coordinate estimate (10) over the chosen coordinate turns its right-hand side into this gap.
--
--   **Formalization Note** $D$ and $\varphi_i^*$ are `EReal`-valued; the left side is the coerced real $P(w)$ minus $D(\alpha)$ in `EReal`.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, proof of Lemma 1, p. 13 (display after (10))

import Mathlib
import Definitions.Def_SDCA_Smooth_Model
open scoped InnerProductSpace

namespace SDCA.Smooth

/-- §7.1, proof of Lemma 1, p. 13 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2): for every dual point
`α` and `w = w(α)`, the duality gap is
`P(w) − D(α) = (1/n) ∑ᵢ (φᵢ(wᵀxᵢ) + φᵢ*(−αᵢ) + αᵢ wᵀxᵢ)`, as an identity in `EReal`
(both sides are `+∞` exactly when some `φᵢ*(−αᵢ) = +∞`). -/
theorem gap_identity {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam) (α : Fin n → ℝ) :
    ((primal lam x φ (wOf lam x α) : ℝ) : EReal) - dual lam x φ α =
      ((1 / (n : ℝ) : ℝ) : EReal) *
        ∑ i, (((φ i ⟪wOf lam x α, x i⟫_ℝ : ℝ) : EReal) + SDCA.Lipschitz.conj (φ i) (-α i) +
          ((α i * ⟪wOf lam x α, x i⟫_ℝ : ℝ) : EReal)) := by sorry

end SDCA.Smooth
