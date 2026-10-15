-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_edge_decomposition
-- name    : SeqLoss.TreeRules.edge_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:24.076485+00:00
-- url     : https://prove2.me/theorems/5cd41093-6f8d-4dfb-af97-f9830b857584
-- title:
--   Proof of Proposition 3, p. 25 — edge-by-edge decomposition φ(T, ℓ) = Σ_{jk∈T} ℓ(jk) φ(T, ℓ_k)
-- statement:
--   Let $\varphi$ be a rule on loss trees that satisfies tree additivity. For an edge $e$ write $\ell_e$ for the loss that is $1$ on $e$ and $0$ everywhere else. Then for every tree $T$ and loss $\ell\ge 0$,
--   $$\varphi_i(T,\ell)=\sum_{e\in T}\ell(e)\,\varphi_i(T,\ell_e)\qquad\text{for each } i\in N(T).$$
--
--   The page writes $\ell_k$ for the unit loss on the edge $jk$. The decomposition reduces every problem to problems with a single unit loss.
--
--   **Formalization Note** The loss $\ell$ is defined on all of $\mathbb N\times\mathbb N$ and need not vanish off $T$; the identity holds as stated, because a rule assigns zero to every agent for losses that vanish on $T$ (balance and non-negativity).
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 25, Appendix A, proof of Proposition 3, first display

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem edge_decomposition (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (hadd : TreeAdditive φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T)
    (ℓ : ℕ × ℕ → ℝ) (hℓ : IsTreeLoss ℓ) :
    ∀ i ∈ N T, φ T ℓ i = ∑ e ∈ T, ℓ e * φ T (Pi.single e 1) i := by sorry

end SeqLoss.TreeRules
