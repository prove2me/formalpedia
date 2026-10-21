-- Prove2me | Theorems.Thm_PosetMarginals_Chains_proposition_4
-- name    : PosetMarginals.Chains.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:41.943303+00:00
-- url     : https://prove2.me/theorems/2740214d-1594-443a-b3db-e54c9e9b24f7
-- title:
--   Proposition 4 — Algorithm 1 uses the maximum necessary total weight
-- statement:
--   Under the standing conditions, when Algorithm 1 terminates after $n^*$ live iterations, the total weight it has assigned is
--   $$\sum_{k=1}^{n^*}w^k=\max\!\left\{\max_{x\in X}\rho_x,\ \max_{C\in\mathcal C}\pi_C\right\}.$$
--
--   This identifies the objective value of the algorithm's feasible (Q) output.
--
--   **Formalization Note** Lean index $k=0$ denotes paper iteration $1$, and the sum runs over $k<n^*$. The theorem requires the final support to be empty and every earlier support nonempty. Both maxima are over finite nonempty sets under the nonempty-poset hypothesis.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, p. 18, Proposition 4; proof pp. 18–19

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Algorithm

namespace PosetMarginals.Chains

/-- Dahan, Amin and Jaillet, Proposition 4, p. 18. Lean state `n` follows `n` paper iterations. -/
theorem proposition_4 {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π)
    (n : ℕ) (hn : (iter ρ π n).X = ∅)
    (hpre : ∀ k < n, (iter ρ π k).X.Nonempty) :
    ∑ k ∈ Finset.range n, (iter ρ π k).w = maxValue ρ π := by sorry

end PosetMarginals.Chains
