-- Prove2me | Theorems.Thm_SeqLoss_LiabilityGame_liabilityGame_convex
-- name    : SeqLoss.LiabilityGame.liabilityGame_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:33.191263+00:00
-- url     : https://prove2.me/theorems/ab2061ba-a6c0-4cd0-8f22-fd77ae9d1427
-- title:
--   Proof of Theorem 3, p. 24 — the liability game $v_\ell$ is convex
-- statement:
--   Let $\ell\in\mathcal L^n$ be a loss problem with $n\ge1$ agents and let $v_\ell$ be its liability game ($v_\ell(S)=\sum_{i\in S}\ell_i$ if the initiator $1\in S$, and $0$ otherwise). Then $v_\ell$ is a **convex game**: $v_\ell(\emptyset)=0$ and for all coalitions $S,T\subseteq N$,
--   $$v_\ell(S)+v_\ell(T)\le v_\ell(S\cup T)+v_\ell(S\cap T).$$
--
--   Convexity is what makes the Shapley value of $v_\ell$ lie in its core and, for big boss games, coincide with the nucleolus (Muto et al. 1988, Theorem 4.5).
--
--   **Formalization Note.** The paper shows convexity in the form of increasing marginal contributions, $v(S\cup\{i\})-v(S)\le v(T\cup\{i\})-v(T)$ for $S\subseteq T$; the statement uses the platform's published `IsConvexGame`, which is the equivalent supermodular form together with $v(\emptyset)=0$. The hypothesis $\ell_i\ge0$ for all $i$ is the paper's $\ell\in\mathcal L^n$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 24, Appendix A, proof of Theorem 3, first paragraph

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game

namespace SeqLoss.LiabilityGame

theorem liabilityGame_convex {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    Supermodularity.Cooperative.IsConvexGame (liabilityGame ℓ) := by sorry

end SeqLoss.LiabilityGame
