-- Prove2me | Theorems.Thm_PosetMarginals_Chains_lemma_3
-- name    : PosetMarginals.Chains.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:39.255357+00:00
-- url     : https://prove2.me/theorems/87c60176-bf63-43cc-8e4b-e53f3990d436
-- title:
--   Lemma 3 — a dropped chain has a dominating surviving chain
-- statement:
--   In a live iteration of Algorithm 1, let $C^{(1)}$ be a maximal chain that is active before the update, absent after the update, and still meets the current positive support $X^k$. Then some chain $C^{(2)}$ remains active after the update, has no larger current slack, and contains every currently positive element of $C^{(1)}$:
--   $$\delta^k_{C^{(2)}}\le\delta^k_{C^{(1)}},\qquad C^{(1)}\cap X^k\subseteq C^{(2)}\cap X^k.$$
--
--   This ensures that removing a chain from the active family does not leave its constraint unaccounted for.
--
--   **Formalization Note** Lean state $k$ is paper iteration $k+1$. The theorem requires supports through that iteration to be nonempty, corresponding to $k_1\in\llbracket1,n^*\rrbracket$.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, p. 15, Lemma 3; proof pp. 15–17

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Algorithm

open Classical

namespace PosetMarginals.Chains

/-- Dahan, Amin and Jaillet, Lemma 3, p. 15. Lean stage `k` is paper stage `k+1`. -/
theorem lemma_3 {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π)
    (k : ℕ) (hk : ∀ j ≤ k, (iter ρ π j).X.Nonempty)
    (C1 : Finset α) (hmax : C1 ∈ maxChains α)
    (hin : C1 ∈ (iter ρ π k).chains)
    (hout : C1 ∉ (iter ρ π (k + 1)).chains)
    (hinter : (C1 ∩ (iter ρ π k).X).Nonempty) :
    ∃ C2 ∈ (iter ρ π (k + 1)).chains,
      (iter ρ π k).δ C2 ≤ (iter ρ π k).δ C1 ∧
      C1 ∩ (iter ρ π k).X ⊆ C2 ∩ (iter ρ π k).X := by sorry

end PosetMarginals.Chains
