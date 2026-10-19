-- Prove2me | Theorems.Thm_PromoMulti_PairwiseExact_higher_order_coef_zero
-- name    : PromoMulti.PairwiseExact.higher_order_coef_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:49.766225+00:00
-- url     : https://prove2.me/theorems/12efb8c8-587a-4ade-88a0-2f5d51d7ae2d
-- title:
--   Appendix, Proof of Theorem 1, pp. 37–39 — with additively separable cross effects, all coefficients of order three and higher vanish
-- statement:
--   Assume the cross-item effects are additively separable, (8). Then for every period $t$ and every pattern $\sigma$ promoting at least three items,
--   $$b^\sigma_t=\sum_{U\subseteq S(\sigma)}(-1)^{|S(\sigma)|-|U|}\,\mathrm{MPOP}\big(\mathbf p^{\sigma|_U}_t\big)=0.$$
--
--   This is the statement the appendix proves by induction on the number of promoted items. Since the App(κ) objective adds the coefficients of order at most κ, it is the whole content of Theorem 1.
--
--   **Formalization Note.** The functions $h$ and $H$ in (8) are arbitrary; no monotonicity, linearity or sign is assumed.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, pp. 37–39 (PDF 37–39), Appendix, Proof of Theorem 1

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact

theorem higher_order_coef_zero {N T : ℕ} (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (t : Fin T) (σ : Pattern I) (h3 : 3 ≤ (supp σ).card) :
    coef I t σ = 0 := by sorry

end PromoMulti.PairwiseExact
