-- Prove2me | Theorems.Thm_SeqLoss_LiabilityGame_theorem_3
-- name    : SeqLoss.LiabilityGame.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:38.831299+00:00
-- url     : https://prove2.me/theorems/d6ed549a-bf2d-4a70-9b73-ec78e23db68c
-- title:
--   Theorem 3 — the midpoint fixed-fraction rule $\varphi^{1/2}(\ell)$ is the Shapley value and the nucleolus of the liability game $v_\ell$
-- statement:
--   Let $\ell=(\ell_1,\dots,\ell_n)\in\mathcal L^n$ be a loss problem with $n\ge1$ agents and total loss $L$, and let $v_\ell$ be its liability game,
--   $$v_\ell(S)=\begin{cases}\sum_{i\in S}\ell_i&\text{if }1\in S,\\ 0&\text{otherwise.}\end{cases}$$
--   Then the allocation of the midpoint fixed-fraction rule,
--   $$\varphi^{1/2}(\ell)=\Bigl(\tfrac12\ell_1+\tfrac12L,\ \tfrac12\ell_2,\ \dots,\ \tfrac12\ell_n\Bigr),$$
--   coincides with both classical point solutions of $v_\ell$:
--   1. it is the **Shapley value** of $v_\ell$: $\mathrm{Sh}(v_\ell)=\varphi^{1/2}(\ell)$;
--   2. it is the **nucleolus** of $v_\ell$: $\varphi^{1/2}(\ell)$ is an imputation of $v_\ell$ whose non-increasingly sorted excess vector is lexicographically minimal among imputations, and it is the only such imputation, i.e. $\nu(v_\ell)=\varphi^{1/2}(\ell)$.
--
--   The theorem gives a game-theoretic foundation for the midpoint $\lambda=1/2$ among the fixed-fraction rules characterized in Theorem 1: the two most prominent single-valued solutions of the liability game both recommend it.
--
--   **Formalization Note.** Agents are `Fin n` with the initiator at index `0`, which needs $n\ge1$ (`[NeZero n]`); the paper's $N=\{1,\dots,n\}$ contains agent 1. The Shapley value is the platform's published `ShapleyValue`. The paper never defines the nucleolus; the standard definition of Schmeidler (1969) is used (definition file `Nucleolus`). The third conjunct (uniqueness) states "$=\nu(v_\ell)$" without relying on Schmeidler's uniqueness theorem.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 15, Theorem 3 (restated p. 24, Appendix A)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game
import Definitions.Def_SeqLoss_LiabilityGame_Nucleolus

namespace SeqLoss.LiabilityGame

theorem theorem_3 {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    Supermodularity.Cooperative.ShapleyValue (liabilityGame ℓ) = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ ∧
    IsNucleolus (liabilityGame ℓ) (SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ) ∧
    ∀ x : Fin n → ℝ, IsNucleolus (liabilityGame ℓ) x → x = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ := by sorry

end SeqLoss.LiabilityGame
