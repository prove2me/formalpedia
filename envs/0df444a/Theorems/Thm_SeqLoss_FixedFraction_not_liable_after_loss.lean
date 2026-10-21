-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_not_liable_after_loss
-- name    : SeqLoss.FixedFraction.not_liable_after_loss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:03.471123+00:00
-- url     : https://prove2.me/theorems/613b41d4-a694-4e88-9c38-8df7f8fc4ea3
-- title:
--   Proof of Proposition 1, p. 22 — under zero truncation, agents after the only loss are not liable
-- statement:
--   Let $\varphi$ be a rule satisfying zero truncation, let $\ell\in L^n$ be a loss vector whose only possibly non-zero entry is $\ell_h$, i.e. $\ell=(0,\dots,0,\ell_h,0,\dots,0)$. Then every agent after $h$ carries no liability:
--   $$\varphi_i(0,\dots,0,\ell_h,0,\dots,0)=0\qquad\text{for all } i>h .$$
--
--   In the proof of Proposition 1 this removes, for a fixed agent $i$, all terms $\varphi_i(0,\dots,0,\ell_h,0,\dots,0)$ with $h<i$ from the decomposition of $\varphi_i(\ell)$.
--
--   **Formalization Note.** Agents are 0-based. The statement assumes only that $\varphi$ is a rule and satisfies zero truncation; additivity, which the surrounding proof also assumes, is not needed.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, Appendix A, p. 22, proof of Proposition 1, (⟹), second display

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

namespace SeqLoss.FixedFraction

theorem not_liable_after_loss (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (hφ : IsRule φ) (hzt : ZeroTruncation φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ)
    (h i : Fin n) (hhi : h < i) (hsingle : ∀ j, j ≠ h → ℓ j = 0) :
    φ n ℓ i = 0 := by sorry

end SeqLoss.FixedFraction
