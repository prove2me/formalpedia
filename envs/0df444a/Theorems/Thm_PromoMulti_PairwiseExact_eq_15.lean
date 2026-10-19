-- Prove2me | Theorems.Thm_PromoMulti_PairwiseExact_eq_15
-- name    : PromoMulti.PairwiseExact.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:50.471971+00:00
-- url     : https://prove2.me/theorems/af77382c-3251-4d85-bfe0-1c13e63ccc19
-- title:
--   Appendix, Proof of Theorem 1, eq. (15), p. 37 — with additively separable cross effects, every three-item coefficient is zero
-- statement:
--   Assume the cross-item effects are additively separable, (8). Let $\sigma$ be a pattern that promotes exactly three items $i,j,k$ at period $t$, with coefficient
--   $$b^{ijk}=\mathrm{MPOP}(i,j,k)-\mathrm{MPOP}(i,j)-\mathrm{MPOP}(i,k)-\mathrm{MPOP}(j,k)+\mathrm{MPOP}(i)+\mathrm{MPOP}(j)+\mathrm{MPOP}(k)-\mathrm{MPOP}(0).\qquad(15)$$
--   Then the contribution $[b^{ijk}]_{\ell,t}$ of each promoted item $\ell\in\{i,j,k\}$ at period $t$ is zero, and $b^{ijk}=0$.
--
--   This is the base case of the induction in the proof of Theorem 1.
--
--   **Formalization Note.** $\mathrm{MPOP}(U)$ is the total profit of the plan promoting only the items of $U$, at their levels in $\sigma$, at period $t$.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, p. 37 (PDF 37), Appendix, Proof of Theorem 1, eq. (15) and the display after it; p. 38 (PDF 38), first sentence

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact

theorem eq_15 {N T : ℕ} (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (t : Fin T) (σ : Pattern I) (h3 : (supp σ).card = 3) :
    (∀ i ∈ supp σ, contrib I t σ i t = 0) ∧ coef I t σ = 0 := by sorry

end PromoMulti.PairwiseExact
