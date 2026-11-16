-- Prove2me | Theorems.Thm_StableVotingDistortion_Supplement_theorem_2
-- name    : StableVotingDistortion.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:56:27.533209+00:00
-- url     : https://prove2.me/theorems/9d2c3890-bfaa-4fd4-bb89-bf8bfbc6d19a
-- title:
--   Theorem 2 — against a maximal lottery every candidate wins with probability at most $1/2$
-- statement:
--   Fix an election with a finite nonempty set of voters $V$ and a finite nonempty set of candidates $C$, and let $D$ be a maximal lottery of the election (Definition 1). Then for every candidate $a$,
--   $$
--   \Pr_{v\sim V,\ b\sim D}[a\succ_v b]\le\frac12 .
--   $$
--   Here $v$ is a uniformly random voter and $b$ a random copy drawn from $D$, with the copy convention (a copy of $a$ drawn against a copy of $a$ wins with probability $1/2$).
--
--   The theorem makes a maximal lottery a randomized analogue of a Condorcet winner: a draw from it beats each fixed candidate for a majority of voters in expectation.
--
--   **Formalization Note** The probability is the uniform voter average of the base mission's `activation` at $g(r)=r$.
--
--   Differences from the source:
--
--   - encoding: Pr_{v∼V, b∼D}[a ≻_v b] under the copy convention → voterMean of the base activation with g(r) = r, i.e. E_v[rank_v(a;D) + D(a)/2]; reason: p.5 copy convention and p.8 Equation (3); same value on every instance
--   - encoding: maximal lottery, the minimax solution of Equation (1) → IsMaximalLottery = IsGStable at g(r) = r; reason: the payoff of a pure attacker is E_v[activation id] (p.8, Equation (3)) and the objective is linear in D†
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 2, p.7

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_Supplement_IsMaximalLottery

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- **Theorem 2.** In any election with maximal lottery `D`, every candidate `a` satisfies
`Pr_{v ∼ V, b ∼ D}[a ≻_v b] ≤ 1/2`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 2, p.7: "In any election with maximal
lottery D, we have Pr_{v∼V, b∼D}[a ≻v b] ≤ 1/2 (2) for all candidates a."

**Formalization Note.** With the copy convention (p.5), `Pr_{b ∼ D}[a ≻_v b]` for a random copy of `a` is the
base mission's `activation (fun r => r) E D v a` (equal to `rank_v(a; D) + D(a)/2` with the left-boundary rank),
and `Pr_{v ∼ V}` is the uniform average `voterMean`. -/
theorem theorem_2 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (E : Election V C) {D : C → ℝ} (hD : IsMaximalLottery E D) (a : C) :
    voterMean (fun v => activation (fun r => r) E D v a) ≤ 1 / 2 := by sorry

end StableVotingDistortion.Supplement
