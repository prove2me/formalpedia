-- Prove2me | Theorems.Thm_PromoMulti_PairwiseExact_locality
-- name    : PromoMulti.PairwiseExact.locality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:47.003961+00:00
-- url     : https://prove2.me/theorems/cc421531-4d67-440c-a9ef-3b4e3aa4a1c0
-- title:
--   Appendix, Proof of Theorem 1, p. 37 — the coefficient splits into item–period contributions, which vanish off the promoted items at time t
-- statement:
--   Fix a period $t$ and a pattern $\sigma$ with support $S$. For an item $i$ and a period $\tau$, write $[b^\sigma_t]_{i,\tau}$ for the contribution of item $i$ at period $\tau$ to the coefficient: the alternating sum over $U\subseteq S$ of $(-1)^{|S|-|U|}$ times the profit $(p^i_\tau-c^i_\tau)d^i_\tau$ of item $i$ at $\tau$ under the plan $\mathbf p^{\sigma|_U}_t$.
--
--   1. The coefficient is the sum of the contributions:
--   $$b^\sigma_t=\sum_{i=1}^N\sum_{\tau=1}^T [b^\sigma_t]_{i,\tau}.$$
--   2. If the cross-item effects are additively separable (8) and $|S|\ge 2$, then $[b^\sigma_t]_{i,\tau}=0$ whenever $\tau\neq t$ or $i\notin S$.
--
--   So only the contributions of the promoted items at the promotion period remain, which reduces the proof of Theorem 1 to one item at one period.
--
--   **Formalization Note.** Part 1 holds for any demand and is stated without (8). In part 2 the functions $h$ and $H$ are arbitrary.
-- source:
--   Cohen, Kalas & Perakis, Promotion Optimization for Multiple Items in Supermarkets, SSRN preprint 3061451, p. 37 (PDF 37), Appendix, Proof of Theorem 1, after (15); p. 38 (PDF 38), after (16)

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact

theorem locality {N T : ℕ} (I : Instance N T) (t : Fin T) (σ : Pattern I) :
    (coef I t σ = ∑ i, ∑ τ, contrib I t σ i τ) ∧
    ∀ (h : (i : Fin N) → Fin T → (Fin (I.M i + 1) → ℝ) → ℝ) (H : Fin N → Fin N → Fin T → ℝ → ℝ),
      AdditiveCross I h H → 2 ≤ (supp σ).card →
      ∀ (i : Fin N) (τ : Fin T), (τ ≠ t ∨ i ∉ supp σ) → contrib I t σ i τ = 0 := by sorry

end PromoMulti.PairwiseExact
