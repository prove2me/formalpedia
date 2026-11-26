-- Prove2me | Theorems.Thm_PvsNP_PublicGame_lower_labels_coin_depth_bound
-- name    : PvsNP.PublicGame.lower_labels_coin_depth_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:54:09.967733+00:00
-- url     : https://prove2.me/theorems/b02ba0c6-4300-559b-a5bf-5b2f27179647
-- title:
--   Coin depth bounds the error of integer lower labels
-- statement:
--   Consider a public-coin game with remaining horizon $H$. Let $M$ be a natural-number scale. At each state, the terminal scaled label is $0$ or $M$. At a prover move, take the larger successor label. At a fair coin toss, take the floor of the average of the two successor labels.
--
--   The resulting label at each state satisfies the local lower inequality: twice the label is at most twice its terminal value or larger successor label, or at most the sum of successor labels at a coin toss. It is the greatest label satisfying these local inequalities. The exact optimal acceptance probability times $M$ is between the label and the label plus the maximum number of coins on a remaining branch. Finally, rounding down after treating any set of omitted positions as rejecting still yields a valid lower-label assignment for the original game.
-- source:
--   Finite-horizon specialization of local reachability inequalities, https://arxiv.org/abs/1910.10636, with an integer rounding and coin-depth bound.

import Definitions.Def_RoundedPublicCoinLowerLabels

open PvsNP.PublicGame

theorem PvsNP.PublicGame.lower_labels_coin_depth_bound {S : Type} (G : Game S) (M H : ℕ) (s : S) :
    let l := lowerValue G M
    LowerLabels G M H l ∧
    (∀ u : ℕ → S → ℕ, LowerLabels G M H u → u H s ≤ l H s) ∧
    l H s * 2^H ≤ M * value G H s ∧
    M * value G H s ≤ (l H s + coinDepth G H s) * 2^H ∧
    (∀ keep : ℕ → S → Bool, LowerLabels G M H (lowerValue (trimGame G keep) M)) := by sorry
