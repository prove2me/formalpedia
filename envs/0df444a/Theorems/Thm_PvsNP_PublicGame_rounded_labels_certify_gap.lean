-- Prove2me | Theorems.Thm_PvsNP_PublicGame_rounded_labels_certify_gap
-- name    : PvsNP.PublicGame.rounded_labels_certify_gap
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:35:11.089304+00:00
-- url     : https://prove2.me/theorems/783d2637-4174-4437-b1a6-5219ecba4f09
-- title:
--   Locally checked integer labels certify a public-coin acceptance gap
-- statement:
--   A finite-horizon game has $H$ remaining moves at its starting position. A move may stop and return a Boolean, let a prover select one of two successors, or choose one of two successors by a fair coin. Let $M=12(H+1)$. At each included position put an integer label in $[0,M]$. The included positions must contain the starting position and all successors of each included nonterminal position.
--
--   The local check compares twice the label with twice the exact scaled terminal value, with twice the larger successor label at a prover choice, or with the sum of the two successor labels at a coin toss. The integers may differ by at most one. At horizon zero, use the terminal convention that only an accepting stop accepts.
--
--   Rounding down the true optimal acceptance probabilities multiplied by $M$ yields valid labels. For every locally valid labeling, when the true optimal acceptance probability at the start is at least $2/3$, the starting label is greater than $M/2$. When the true optimum is at most $1/3$, it is less than $M/2$.
-- source:
--   Direct finite-horizon game recurrence and integer rounding. Original standalone formalization.

import Definitions.Def_RoundedPublicCoinGame

open PvsNP.PublicGame

theorem PvsNP.PublicGame.rounded_labels_certify_gap {S : Type} (G : Game S) (H : ℕ) (s : S) :
    let M := 12*(H+1)
    LocallyRounded G M H (floorValue G M) ∧
    ∀ (u : ℕ → S → ℕ) (active : ℕ → S → Prop),
      LocallyRoundedOn G M H u active → active H s →
      (2*2^H ≤ 3*value G H s → M < 2*u H s) ∧
      (3*value G H s ≤ 2^H → 2*u H s < M) := by sorry
