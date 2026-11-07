-- Prove2me | Theorems.Thm_StableVotingDistortion_theorem_1
-- name    : StableVotingDistortion.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:49.417179+00:00
-- url     : https://prove2.me/theorems/31ca946f-eb10-413c-9301-fff0c2644bd2
-- title:
--   Theorem 1 — a continuous activation $g$ exists for which every $g$-stable lottery has distortion at most $2.1248$
-- statement:
--   There exists a continuous, non-decreasing function $g:[0,1]\to[0,1]$ with $g(0)=0$ and $g(1)=1$ such that in any election $E$ a $g$-stable lottery exists, and every $g$-stable lottery $D$ satisfies, for every pseudometric $d$ consistent with $E$ and every candidate $a$,
--   $$\mathrm{cost}_d(D)\le2.1248\cdot\mathrm{cost}_d(a).$$
--
--   The function $g$ is chosen once, before the election. The lower bound for any randomized voting rule is $2.11264$, so this comes within $0.013$ of it.
--
--   Differences from the source:
--   - reading: p.11: "every $g$-stable lottery has distortion at most 2.1248"; p.3: "There is a randomized voting rule with distortion at most 2.1248" → also `∃ D, IsGStable g E D` for each election; reason: the bound alone would be vacuous on an election with no $g$-stable lottery; p.4 states existence, and with it the p.3 form follows
--   - reading: distortion at most $B$, as the ratio $\mathrm{cost}_d(D)/\min_a\mathrm{cost}_d(a)$ → `HasDistortionAtMost`: $\mathrm{cost}_d(D)\le B\,\mathrm{cost}_d(a)$ for all consistent $d$ and all candidates $a$; reason: the same for a positive minimum; it avoids division by zero, and with a zero minimum it forces $\mathrm{cost}_d(D)=0$
--   - reading: $g(\mathrm{rank}_v(a;D))$, with $\mathrm{rank}_v$ overloaded on p.8 → `activation`: the average of $g$ over $a$'s interval if $D(a)\neq0$, and $g$ at the left boundary if $D(a)=0$; reason: p.8 makes the attacker's rank a uniformly random point of its interval, p.22 gives the zero-mass value, and the proof of Theorem 4 needs a uniformly random rank under $a\sim D$
--   - encoding: $D_g$ solves $\arg\min_D\max_{D^\dagger}$ → `IsGStable`: $D$ in `stdSimplex ℝ C` minimizes $H(D)=\max_{a\in C}$ over lotteries; reason: p.11: the maximum over $D^\dagger$ of a linear objective equals $H(D)$
--   - encoding: a pseudometric on $V\cup C$ → `d : V ⊕ C → V ⊕ C → ℝ` with `IsPseudometric`; reason: a sum type tags voters and candidates; a voter and a candidate may be at distance $0$
--   - encoding: $g:[0,1]\to[0,1]$ → a function `ℝ → ℝ` with `IsActivation g`, constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 1, p.11; also p.3

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_IsGStable

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Theorem 1.** There exists a continuous, non-decreasing `g : [0, 1] → [0, 1]` with `g(0) = 0`, `g(1) = 1`
such that in any election a `g`-stable lottery exists, and every `g`-stable lottery has distortion at most
`2.1248`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 1, p.11: "There exists a continuous, non-decreasing function g : [0, 1] → [0, 1] with
g(0) = 0, g(1) = 1, such that in any election, every g-stable lottery has distortion at most 2.1248."; p.3:
"There is a randomized voting rule with distortion at most 2.1248."

**Formalization Note.** `g` is chosen once, before the election. The existence clause keeps "every `g`-stable
lottery" from being vacuous, and with it the p.3 form follows. Distortion is the inequality
`HasDistortionAtMost`, so a zero optimum is not excluded. -/
theorem theorem_1 :
    ∃ g : ℝ → ℝ, IsActivation g ∧ g 0 = 0 ∧ g 1 = 1 ∧
      ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C),
        (∃ D : C → ℝ, IsGStable g E D) ∧
          ∀ D : C → ℝ, IsGStable g E D → HasDistortionAtMost E D 2.1248 := by sorry

end StableVotingDistortion
