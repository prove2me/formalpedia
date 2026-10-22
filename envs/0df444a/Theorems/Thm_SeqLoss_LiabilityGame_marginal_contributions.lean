-- Prove2me | Theorems.Thm_SeqLoss_LiabilityGame_marginal_contributions
-- name    : SeqLoss.LiabilityGame.marginal_contributions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:30.95108+00:00
-- url     : https://prove2.me/theorems/6337c98c-f0b2-4cab-aa43-51dd52dcd087
-- title:
--   Proof of Theorem 3, p. 24 — contributions to the grand coalition: $M_1(v_\ell)=L$ and $M_i(v_\ell)=\ell_i$ for $i\neq1$
-- statement:
--   Let $\ell\in\mathcal L^n$ with $n\ge1$, total loss $L=\sum_i\ell_i$, and liability game $v_\ell$. The contributions $M_i(v_\ell)=v_\ell(N)-v_\ell(N\setminus\{i\})$ of the agents to the grand coalition are
--   $$M_1(v_\ell)=L,\qquad M_i(v_\ell)=\ell_i\quad\text{for every } i\neq 1.$$
--
--   These are the quantities in Muto et al.'s (1988) formula for the nucleolus of a big boss game, which gives the non-initiators half of their contribution.
--
--   **Formalization Note.** The initiator is index `0`. The hypothesis $\ell\in\mathcal L^n$ is the paper's standing one and is kept, although the identities do not need it.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 24, Appendix A, proof of Theorem 3, second paragraph, first sentence

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game

namespace SeqLoss.LiabilityGame

theorem marginal_contributions {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    marginalContribution (liabilityGame ℓ) 0 = SeqLoss.FixedFraction.total ℓ ∧
    ∀ i : Fin n, i ≠ 0 → marginalContribution (liabilityGame ℓ) i = ℓ i := by sorry

end SeqLoss.LiabilityGame
