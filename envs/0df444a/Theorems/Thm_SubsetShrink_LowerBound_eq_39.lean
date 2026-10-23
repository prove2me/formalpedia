-- Prove2me | Theorems.Thm_SubsetShrink_LowerBound_eq_39
-- name    : SubsetShrink.LowerBound.eq_39
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:05.217984+00:00
-- url     : https://prove2.me/theorems/82397272-fa07-499b-b7eb-4d0f8cba292b
-- title:
--   Proof of Theorem 4 (B.9), p. 44 — the G(β) identity, G(β) = H(β_{S̃ᶜ}) and (39)
-- statement:
--   Let $X$ be a real $n\times p$ matrix, $k$ a nonnegative integer, $\beta^*,\tilde\beta^*\in\mathbb R^p$ and $\epsilon\in\mathbb R^n$, with $\|\tilde\beta^*\|_0\le k/2$. Put $y=X\beta^*+\epsilon$, $\Delta^*=X\beta^*-X\tilde\beta^*$, $\tilde S=\operatorname{supp}(\tilde\beta^*)$, and
--   $$
--   G(\beta)=\|y-X\beta\|^2-\|y-X\tilde\beta^*\|^2,\qquad H(u)=\|Xu\|^2-2(\Delta^*+\epsilon)^\top Xu .
--   $$
--   Then:
--
--   1. for every $\beta\in\mathbb R^p$,
--   $$
--   G(\beta)=\|X\beta-X\tilde\beta^*\|^2+2(\Delta^*+\epsilon)^\top(X\tilde\beta^*-X\beta);
--   $$
--   2. if $\beta$ agrees with $\tilde\beta^*$ on $\tilde S$ and $\|\beta\|_0\le k$, then $G(\beta)=H(\beta_{\tilde S^c})$, where $\beta_{\tilde S^c}$ keeps the coordinates of $\beta$ outside $\tilde S$ and sets the others to $0$;
--   3. for every $u$ with $\operatorname{supp}(u)\subseteq\tilde S^c$ and $\|u\|_0\le k/2$ there is $\beta$ with $\|\beta\|_0\le k$ that agrees with $\tilde\beta^*$ on $\tilde S$ and satisfies $G(\beta)\le H(u)$.
--
--   Part 3 is the chain (39), $\min_{\|\beta\|_0\le k}G(\beta)\le\min_{\operatorname{supp}(u)\subseteq\tilde S^c,\,\|u\|_0\le k/2}H(u)$, stated for each $u$. It reduces the best-subsets objective, recentred at the sparse approximation $\tilde\beta^*$, to a quadratic function of a vector supported off $\tilde S$.
--
--   **Formalization Note** The minima of (39) are written pointwise ("for every $u$ there is $\beta$"), which is equivalent and avoids real infima. "$\beta_{\tilde S}=\tilde\beta^*$" is read as "$\beta_j=\tilde\beta^*_j$ for $j\in\tilde S$", which is the same since $\tilde\beta^*$ vanishes off $\tilde S$. $\|\cdot\|_0\le k/2$ is a real comparison. No assumption on the columns of $X$ is needed.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 44, proof of Theorem 4 (B.9), the display defining G(β), the display G(β) = H(β_{S̃ᶜ}), and (39)

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SubsetShrink.LowerBound

/-- Proof of Theorem 4, p. 44: the identity for `G`, the reduction `G(β) = H(β_{S̃ᶜ})` when
`β_{S̃} = β̃*`, and (39) in pointwise form. Here `y = Xβ* + ε`, `Δ* = Xβ* − Xβ̃*`, `S̃ = supp β̃*`
and `‖β̃*‖₀ ≤ k/2`. -/
theorem eq_39 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (βstar βt : Fin p → ℝ) (ε : Fin n → ℝ) (hβt : (l0 βt : ℝ) ≤ (k : ℝ) / 2) :
    (∀ β : Fin p → ℝ,
      Gfun X (X.mulVec βstar + ε) βt β =
        ∑ i, (X.mulVec β i - X.mulVec βt i) ^ 2 +
          2 * SubsetShrink.Events.dot (X.mulVec βstar - X.mulVec βt + ε) (X.mulVec βt - X.mulVec β)) ∧
    (∀ β : Fin p → ℝ, (∀ j ∈ supp βt, β j = βt j) → l0 β ≤ k →
      Gfun X (X.mulVec βstar + ε) βt β =
        Hfun X (X.mulVec βstar - X.mulVec βt + ε) (restrict β (supp βt)ᶜ)) ∧
    (∀ u : Fin p → ℝ, supp u ⊆ (supp βt)ᶜ → (l0 u : ℝ) ≤ (k : ℝ) / 2 →
      ∃ β : Fin p → ℝ, l0 β ≤ k ∧ (∀ j ∈ supp βt, β j = βt j) ∧
        Gfun X (X.mulVec βstar + ε) βt β ≤ Hfun X (X.mulVec βstar - X.mulVec βt + ε) u) := by sorry

end SubsetShrink.LowerBound
