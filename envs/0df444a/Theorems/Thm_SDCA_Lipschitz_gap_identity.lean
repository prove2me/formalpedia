-- Prove2me | Theorems.Thm_SDCA_Lipschitz_gap_identity
-- name    : SDCA.Lipschitz.gap_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:11:45.923762+00:00
-- url     : https://prove2.me/theorems/db19985c-eb01-47a0-8997-896e68d82d02
-- title:
--   §7.1, p. 13 — the duality gap $P(w(\alpha))-D(\alpha)=\frac1n\sum_i(\phi_i(w^\top x_i)+\phi_i^*(-\alpha_i)+\alpha_iw^\top x_i)$
-- statement:
--   Throughout, $x_1,\dots,x_n\in\mathbb R^d$ ($n\ge1$), $\phi_1,\dots,\phi_n:\mathbb R\to\mathbb R$ are convex, $\lambda>0$, $P$ is the primal objective (1), $D$ the dual objective (2), $\phi_i^*$ the convex conjugate and $w(\alpha)=\frac1{\lambda n}\sum_i\alpha_ix_i$.
--
--   For every $\alpha\in\mathbb R^n$ and $w=w(\alpha)$,
--   $$P(w)-D(\alpha)=\frac1n\sum_{i=1}^n\Bigl(\phi_i(w^\top x_i)+\phi_i^*(-\alpha_i)+\alpha_i\,w^\top x_i\Bigr).$$
--
--   The identity writes the duality gap as an average of Fenchel–Young gaps, one per example; it converts the averaged one-step bound (10) into Lemma 1.
--
--   **Formalization Note** The identity is stated in `EReal`, so it holds for every $\alpha$: when some $\phi_i^*(-\alpha_i)=+\infty$, both sides are $+\infty$. The paper's display is written for $w$ with $\lambda w^\top w=\frac1n\sum_i\alpha_iw^\top x_i$, which holds for $w=w(\alpha)$; the statement is made for $w=w(\alpha)$.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, §7.1, proof of Lemma 1, p. 13, unnumbered display after (10)

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

namespace SDCA.Lipschitz

/-- §7.1, proof of Lemma 1, p. 13 (unnumbered display): for every dual vector `α` and
`w = w(α)`, the duality gap is
`P(w) − D(α) = (1/n) ∑ᵢ (φᵢ(wᵀxᵢ) + φᵢ*(−αᵢ) + αᵢ wᵀxᵢ)`, in `EReal`
(both sides are `⊤` when some `φᵢ*(−αᵢ) = ⊤`). -/
theorem gap_identity {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (α : Fin n → ℝ) :
    ((primal φ x lam (wOf x lam α) : ℝ) : EReal) - dual φ x lam α =
      (((1 / (n : ℝ)) : ℝ) : EReal) *
        ∑ i, (((φ i (inner ℝ (wOf x lam α) (x i)) + α i * inner ℝ (wOf x lam α) (x i) : ℝ) : EReal)
          + conj (φ i) (-α i)) := by sorry

end SDCA.Lipschitz
