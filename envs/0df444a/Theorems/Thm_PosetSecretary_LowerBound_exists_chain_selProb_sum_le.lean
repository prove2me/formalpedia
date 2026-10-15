-- Prove2me | Theorems.Thm_PosetSecretary_LowerBound_exists_chain_selProb_sum_le
-- name    : PosetSecretary.LowerBound.exists_chain_selProb_sum_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:13.022008+00:00
-- url     : https://prove2.me/theorems/b4c08536-0913-426a-83e7-bc478a2c1cd8
-- title:
--   Proof of Proposition 5.1, p. 42 — some chain i has Σ_j p_j^i ≤ k/ω
-- statement:
--   Let $\omega\ge1$ and $k\ge0$, and let $\mu$ be a selection rule with capacity $k$ on $\mathrm{Chains}(\omega,k)$, the disjoint union of $\omega$ chains of $k$ elements. Write $p^i_j$ for the probability that $\mu$ selects the element $(i,j)$. Then some chain $i$ satisfies
--   $$\sum_{j}p^i_j\le\frac{k}{\omega}.$$
--
--   The least-selected chain is the one the lower-bound construction loads with the score.
--
--   **Formalization Note** The page indexes the elements of a chain by rank ("the $j$th best"); the sum over all elements of a chain does not depend on that indexing.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.1, Appendix F, p. 42, second paragraph

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting

namespace PosetSecretary.LowerBound

theorem exists_chain_selProb_sum_le (ω k : ℕ) (hω : 1 ≤ ω)
    (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) :
    ∃ i : Fin ω, ∑ j : Fin k, selProb μ ⟨i, j⟩ ≤ (k : ℝ) / ω := by sorry

end PosetSecretary.LowerBound
