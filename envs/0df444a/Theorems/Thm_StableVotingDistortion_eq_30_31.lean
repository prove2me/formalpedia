-- Prove2me | Theorems.Thm_StableVotingDistortion_eq_30_31
-- name    : StableVotingDistortion.eq_30_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:43.388075+00:00
-- url     : https://prove2.me/theorems/5f271d05-c1ad-4ebc-a0df-24681705288f
-- title:
--   Equations (30)–(31) — the two consequences of stability
-- statement:
--   Let $\lambda\in(0,1)$, let $\phi$ satisfy (26), and let $D$ be a $g_\phi$-stable lottery. Then every set $S$ of candidates has expected score zero across voters,
--   $$\mathbb E_v\Bigl[\sum_{b\in S}\int_{\mathrm{rank}_v(b)}^{\mathrm{rank}_v(b)+D(b)}(-\phi)\Bigr]=0,$$
--   in particular $\mathbb E_v[k_v(t)]=0$; and for $s_v$ the left endpoint of any candidate's interval,
--   $$\mathbb E_v[\phi(s_v)]\ge0.$$
--
--   Differences from the source:
--   - generalization: $\mathbb E_v[k_v(t)]=0$ for the slice $S_t$ → the same for every `S : Finset C`; reason: $S_t$ is the instance `St ρ t`, and the page's argument is linearity over candidates
--   - generalization: $s_v$ the left endpoint of $a^\star$'s interval → the left endpoint of any candidate's interval; reason: $a^\star$ is an instance; nothing in (31) uses its optimality
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (30), (31), p.28

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Equations (30)–(31).** For a `g_ϕ`-stable lottery under (26): every set `S` of candidates has
`E_v[score of S on v's rank line] = 0`, and for `s_v` the left boundary of any candidate,
`E_v[ϕ(s_v)] ≥ 0`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (30), (31), p.28: "linearity of expectation shows that the total score k_v(t) of S_t
on v's rank line satisfies E_v[k_v(t)] = 0. (30) Second, since ϕ is nonincreasing, its value at the left
endpoint s_v of a⋆'s interval is at least its average over that interval; as a⋆ has expected score at most
zero (Theorem 4), this gives E_v[ϕ(s_v)] ≥ 0. (31)"

**Formalization Note.** (30) is stated for every subset of `C`; `S_t` is the instance `St ρ t`, and
`blockScore E D ϕ v (St ρ t)` is `kv E D ρ ϕ v t` by definition. -/
theorem eq_30_31 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ) {D : C → ℝ} (hD : IsGStable (gPhi ϕ) E D) :
    (∀ S : Finset C, voterMean (fun v => blockScore E D ϕ v S) = 0) ∧
      ∀ a : C, 0 ≤ voterMean (fun v => ϕ (sv E D a v)) := by sorry

end StableVotingDistortion
