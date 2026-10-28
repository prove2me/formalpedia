-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_scale_invariance
-- name    : SeqLoss.TreeRules.scale_invariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:26.042017+00:00
-- url     : https://prove2.me/theorems/4087c0d7-cd1f-4cc0-bafe-529a7c8ec317
-- title:
--   Proof of Proposition 3, p. 25 — tree additivity and continuity imply scale invariance
-- statement:
--   Let $\varphi$ be a rule on loss trees (non-negative, balanced, label-invariant and continuous) that satisfies tree additivity. Then for every tree $T$, loss $\ell\ge 0$ and $\alpha\ge 0$,
--   $$\varphi_i(T,\alpha\ell)=\alpha\,\varphi_i(T,\ell)\qquad\text{for each } i\in N(T).$$
--
--   This is the tree analogue of Lemma 1 and the first step of the proof of Proposition 3: it lets a loss on one edge be normalized to $1$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 25, Appendix A, proof of Proposition 3, first sentence after 'Let T ∈ 𝒯'

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

namespace SeqLoss.TreeRules

theorem scale_invariance (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (hadd : TreeAdditive φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T)
    (ℓ : ℕ × ℕ → ℝ) (hℓ : IsTreeLoss ℓ) (α : ℝ) (hα : 0 ≤ α) :
    ∀ i ∈ N T, φ T (α • ℓ) i = α * φ T ℓ i := by sorry

end SeqLoss.TreeRules
