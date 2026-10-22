-- Prove2me | Theorems.Thm_PromoMulti_PairwiseExact_theorem_1
-- name    : PromoMulti.PairwiseExact.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:50.709252+00:00
-- url     : https://prove2.me/theorems/33bcba79-0a17-4c15-90a0-c4de65d6fa1b
-- title:
--   Theorem 1, p. 14 (PDF 14) — with additively separable cross-item effects (8), App(2) = App(3) = … = App(N)
-- statement:
--   Consider the multi-item promotion model with $N$ items and $T$ periods, and assume that the cross-item effects of every item are additively separable:
--   $$d^i_t\big(p^i_t,p^i_{t-1},\dots,p^i_{t-M^i},\mathbf p^{-i}_t\big)=h^i_t\big(p^i_t,p^i_{t-1},\dots,p^i_{t-M^i}\big)+\sum_{j\neq i}H^{ji}_t(p^j_t)\qquad(8)$$
--   for arbitrary functions $h^i_t$ and $H^{ji}_t$. Then $\mathrm{App}(2)=\mathrm{App}(3)=\dots=\mathrm{App}(N)$. Precisely, for every $\kappa$ with $2\le\kappa\le N$ and every choice of business-rule data $(L^i,S^i,L_T,C_t)$:
--
--   1. the App(κ) and App(2) objectives agree at every plan $\gamma$;
--   2. a plan is an optimal solution of App(κ) (feasible for (Multi-POP) and maximizing the App(κ) objective over the feasible plans) if and only if it is an optimal solution of App(2).
--
--   Hence it suffices to consider the unilateral and pairwise contributions to capture all cross-item effects. App(2) is not claimed to solve (Multi-POP) itself: when past prices matter, App(N) is in general not exact either.
--
--   **Formalization Note.** App(κ) and App(2) have the same feasible set, so "App(2) = App(κ)" is stated as equality of objectives at every plan together with equality of the sets of optimal plans; no optimal value is formed with a supremum. The App(κ) objective uses, for integral plans, the product reading of the pairwise and higher variables forced by the consistency constraints (7). Prices before period 1 are $q^0$; the theorem holds for any fixed price history.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, p. 14 (PDF 14), Theorem 1

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact

theorem theorem_1 {N T : ℕ} (I : Instance N T)
    (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ)
    (hsep : AdditiveCross I h H) (R : Rules N T) (κ : ℕ) (hκ : 2 ≤ κ) (hκN : κ ≤ N) :
    (∀ γ : Plan I, appObj I κ γ = appObj I 2 γ) ∧
    (∀ γ : Plan I, IsOptimalApp I R κ γ ↔ IsOptimalApp I R 2 γ) := by sorry

end PromoMulti.PairwiseExact
