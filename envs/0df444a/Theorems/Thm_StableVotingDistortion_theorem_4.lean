-- Prove2me | Theorems.Thm_StableVotingDistortion_theorem_4
-- name    : StableVotingDistortion.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:03.357691+00:00
-- url     : https://prove2.me/theorems/f55c3693-f0b7-4771-a90f-65b4dbb67625
-- title:
--   Theorem 4 — a $g$-stable lottery gives every candidate expected activation at most $\int_0^1 g$
-- statement:
--   Let $g:[0,1]\to[0,1]$ be continuous and non-decreasing, let $E$ be an election and $D_g$ a $g$-stable lottery. Then for every candidate $a$,
--   $$\mathbb E_{v\sim V}[g(\mathrm{rank}_v(a;D_g))]\le\int_0^1g(t)\,dt.$$
--
--   This is the guarantee stability gives against an attacker, including candidates outside the lottery's support.
--
--   Differences from the source:
--   - reading: $g(\mathrm{rank}_v(a;D))$, with $\mathrm{rank}_v$ overloaded on p.8 → `activation`: the average of $g$ over $a$'s interval if $D(a)\neq0$, and $g$ at the left boundary if $D(a)=0$; reason: p.8 makes the attacker's rank a uniformly random point of its interval, p.22 gives the zero-mass value, and the proof of Theorem 4 needs a uniformly random rank under $a\sim D$
--   - encoding: $D_g$ solves $\arg\min_D\max_{D^\dagger}$ → `IsGStable`: $D$ in `stdSimplex ℝ C` minimizes $H(D)=\max_{a\in C}$ over lotteries; reason: p.11: the maximum over $D^\dagger$ of a linear objective equals $H(D)$
--   - encoding: $g:[0,1]\to[0,1]$ → a function `ℝ → ℝ` with `IsActivation g`, constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 4, p.10

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_activation
import Definitions.Def_StableVotingDistortion_IsGStable

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Theorem 4.** In any election, a `g`-stable lottery gives every candidate expected activation at most
`∫_0^1 g`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 4, p.10: "In any election with g-stable lottery D_g, we have
E_{v∼V}[g(rank_v(a; D_g))] ≤ ∫_0^1 g(t) dt. (10) for all candidates a."

**Formalization Note.** `g(rank_v(a; D))` is the attacker's random-copy rank, `activation`. -/
theorem theorem_4 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] {g : ℝ → ℝ}
    (hg : IsActivation g) (E : Election V C) {D : C → ℝ} (hD : IsGStable g E D) (a : C) :
    voterMean (fun v => activation g E D v a) ≤ ∫ t in (0 : ℝ)..1, g t := by sorry

end StableVotingDistortion
