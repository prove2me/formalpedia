-- Prove2me | Theorems.Thm_PromoMulti_PairwiseExact_eq_16
-- name    : PromoMulti.PairwiseExact.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:45.119991+00:00
-- url     : https://prove2.me/theorems/1a607b77-668b-47f4-9a65-156338ad1491
-- title:
--   Appendix, Proof of Theorem 1, p. 38 — each coefficient is MPOP(S) − MPOP(0) minus all lower-order coefficients
-- statement:
--   Let $\sigma$ be a pattern promoting a nonempty set of items $S=S(\sigma)$ at period $t$. Then the coefficient $b^\sigma_t$ equals the total profit of promoting $S$ at $t$, minus the regular profit, minus the coefficients of all proper nonempty sub-patterns:
--   $$b^\sigma_t=\mathrm{MPOP}(\mathbf p^\sigma_t)-\mathrm{MPOP}(\mathbf p^0)-\sum_{\emptyset\neq U\subsetneq S} b^{\sigma|_U}_t.$$
--   For two items this is the remark on p. 13, $b^{k\ell ju}_t=\mathrm{MPOP}(\mathbf p^{k\ell ju}_t)-\mathrm{MPOP}(\mathbf p^0)-b^{kj}_t-b^{\ell u}_t$; for $K$ items it is the display before (16) on p. 38.
--
--   The identity holds for every demand function. It is the bridge between the closed alternating-sum form of the coefficients and the recursive form used in the induction of the proof of Theorem 1, where the induction hypothesis removes the terms of order at least three and leaves (16).
--
--   **Formalization Note.** The nonemptiness of $S$ is needed: for the empty pattern the coefficient is $\mathrm{MPOP}(\mathbf p^0)$ and the right-hand side is $0$. The paper's coefficients always have at least one promoted item.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, p. 38 (PDF 38), Appendix, Proof of Theorem 1, display preceding (16); p. 13 (PDF 13), remark after (6)

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact

theorem eq_16 {N T : ℕ} (I : Instance N T) (t : Fin T) (σ : Pattern I)
    (hσ : (supp σ).Nonempty) :
    coef I t σ = MPOP I (pure I t σ) - MPOP I (regular I) -
      ∑ U ∈ (supp σ).powerset.filter (fun U => U.Nonempty ∧ U ≠ supp σ),
        coef I t (restrict σ U) := by sorry

end PromoMulti.PairwiseExact
