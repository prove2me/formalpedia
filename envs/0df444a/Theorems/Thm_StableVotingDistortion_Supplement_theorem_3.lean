-- Prove2me | Theorems.Thm_StableVotingDistortion_Supplement_theorem_3
-- name    : StableVotingDistortion.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:56:57.791949+00:00
-- url     : https://prove2.me/theorems/6b3793e5-ac7e-4cfc-adc1-9abebfd68d52
-- title:
--   Theorem 3 — against a stable $k$-lottery a candidate beats $k$ draws with probability at most $1/(k+1)$
-- statement:
--   Fix an election with finite nonempty voter and candidate sets, an integer $k\ge1$, and a stable $k$-lottery $D$ (Definition 2). Then for every candidate $a$,
--   $$
--   \Pr_{v\sim V,\ b_1,\dots,b_k\sim D}[a\succ_v b_1,\dots,b_k]\le\frac1{k+1}.
--   $$
--   The voter $v$ is uniform and $b_1,\dots,b_k$ are independent copies drawn from $D$, with the copy convention.
--
--   The bound $1/(k+1)$ is the value of the $k$ vs $1$ Condorcet game; it is the property of stable $k$-lotteries used in the analysis of their distortion.
--
--   **Formalization Note** The probability is the uniform voter average of the base mission's `activation` at $g(r)=r^k$, which is $\mathbb E_v[\mathrm{rank}_v(a;D)^k]$ with the random-copy rank (p.9).
--
--   Differences from the source:
--
--   - encoding: Pr_{v∼V, b1..bk∼D}[a ≻_v b1, …, bk] under the copy convention → voterMean of the base activation with g(r) = r^k; reason: p.9, the display before Equation (6); same value on every instance
--   - encoding: stable k-lottery, the minimax solution of Equation (4) → IsStableKLottery k = IsGStable at g(r) = r^k; reason: Equations (6)–(7), p.9: the payoff of a pure attacker is E_v[rank_v(a;D)^k] and the objective is linear in D†
--   - encoding: integer k ≥ 1 → k : ℕ with 1 ≤ k; reason: same values
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 3, p.9

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_Supplement_IsStableKLottery

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- **Theorem 3.** In any election with stable `k`-lottery `D` (`k ≥ 1`), every candidate `a` satisfies
`Pr_{v ∼ V, b₁, …, b_k ∼ D}[a ≻_v b₁, …, b_k] ≤ 1/(k + 1)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 3, p.9: "In any election with stable
k-lottery D, we have Pr_{v∼V, b1,...,bk∼D}[a ≻v b1, . . . , bk] ≤ 1/(k + 1). (5) for all candidates a."

**Formalization Note.** With the copy convention (p.5), the probability that a random copy of `a` beats `k`
independent draws from `D` is `rank_v(a; D)^k` with the random-copy rank, the base mission's
`activation (fun r => r ^ k) E D v a` (p.9, the display before Equation (6)). `k` is a natural number with
`1 ≤ k`. -/
theorem theorem_3 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    {k : ℕ} (hk : 1 ≤ k) (E : Election V C) {D : C → ℝ} (hD : IsStableKLottery k E D) (a : C) :
    voterMean (fun v => activation (fun r => r ^ k) E D v a) ≤ 1 / ((k : ℝ) + 1) := by sorry

end StableVotingDistortion.Supplement
