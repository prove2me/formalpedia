-- Prove2me | Theorems.Thm_SeqLoss_LiabilityGame_shapley_is_nucleolus
-- name    : SeqLoss.LiabilityGame.shapley_is_nucleolus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:27.167965+00:00
-- url     : https://prove2.me/theorems/c481f882-7bc3-43a1-b265-30a7bb931504
-- title:
--   Proof of Theorem 3, p. 24 — the Shapley value of the convex big boss game $v_\ell$ is its nucleolus
-- statement:
--   Let $\ell\in\mathcal L^n$ with $n\ge1$ and let $v_\ell$ be the liability game. Then the Shapley value of $v_\ell$,
--   $$\mathrm{Sh}_i(v_\ell)=\sum_{S\subseteq N\setminus\{i\}}\frac{|S|!\,(n-|S|-1)!}{n!}\bigl(v_\ell(S\cup\{i\})-v_\ell(S)\bigr),$$
--   is the nucleolus of $v_\ell$: it is an imputation, and no imputation has a lexicographically smaller non-increasingly sorted excess vector.
--
--   The paper derives this from Muto et al. (1988, Theorem 4.5): for a big boss game that is convex, the Shapley value and the nucleolus coincide.
--
--   **Formalization Note.** The Shapley value is the platform's published `Supermodularity.Cooperative.ShapleyValue`; its natural-number subtraction $n-|S|-1$ is exact because $S\subseteq N\setminus\{i\}$ has $|S|\le n-1$. The nucleolus is `IsNucleolus` of this mission's definition file.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 24, Appendix A, proof of Theorem 3, last sentence (citing Muto, Nakayama, Potters & Tijs 1988, Theorem 4.5)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game
import Definitions.Def_SeqLoss_LiabilityGame_Nucleolus

namespace SeqLoss.LiabilityGame

theorem shapley_is_nucleolus {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    IsNucleolus (liabilityGame ℓ)
      (Supermodularity.Cooperative.ShapleyValue (liabilityGame ℓ)) := by sorry

end SeqLoss.LiabilityGame
