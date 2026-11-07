-- Prove2me | Theorems.Thm_StableVotingDistortion_W_nonneg_monotone
-- name    : StableVotingDistortion.W_nonneg_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:46.220297+00:00
-- url     : https://prove2.me/theorems/8a737369-8c32-46a5-9f5c-992ed85e6e89
-- title:
--   Equations (34)–(35) — the potentials $W_x$ and $W$ are nonnegative and nondecreasing
-- statement:
--   Let $\lambda\in(0,1)$, let $\phi$ satisfy (26), and let $\phi(z)+z$ be nonincreasing on $[\lambda,1]$. Then for each $x\in[0,\lambda)$, the function $W_x$ of (34) is nonnegative and nondecreasing on $[0,1]$. Moreover for any election, lottery and candidate $a^\star$ with $A>0$, the function $W$ of (35) is nonnegative and nondecreasing on $[0,1]$.
--
--   Differences from the source:
--   - generalization: §6.3.1's setting: $D$ a $g_\phi$-stable lottery (for $W$ of (35)) → any lottery `D ∈ stdSimplex ℝ C` with $A>0$; reason: $W$ is a $\phi(s_v)$-weighted average of the $W_x$, and the argument of p.29 uses only (26) and $\phi+r$ nonincreasing; a $g_\phi$-stable lottery is a lottery, so the statement specializes to the page's
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (34), (35), p.29

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices
import Definitions.Def_StableVotingDistortion_offset

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Equations (34)–(35): the potentials.** Under (26) with `ϕ(z) + z` nonincreasing on `[λ, 1]`: for each
`x ∈ [0, λ)`, `W_x` is nonnegative and nondecreasing on `[0, 1]`; and for any lottery with `A > 0`, so is `W`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (34), (35), p.29: "Because 0 < ϕ(x) ≤ λ − x by Equation (26), the line through
(x, ϕ(x)) and (λ, 0) has slope at least −1. Provided that ϕ(z) + z is nonincreasing on [λ, 1], ϕ falls at
least as steeply as this line beyond λ, so the horizontal gap W_x(z) between them in Figure 10 is
nonnegative and grows with z. Hence W is nonnegative and nondecreasing." -/
theorem W_nonneg_monotone {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1)) :
    (∀ x ∈ Set.Ico 0 lam, (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Wx lam ϕ x z) ∧
        MonotoneOn (Wx lam ϕ x) (Set.Icc 0 1)) ∧
      ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ), D ∈ stdSimplex ℝ C → ∀ aStar : C,
        0 < Aval lam ϕ E D aStar →
          (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ WAvg lam ϕ E D aStar z) ∧
            MonotoneOn (WAvg lam ϕ E D aStar) (Set.Icc 0 1) := by sorry

end StableVotingDistortion
