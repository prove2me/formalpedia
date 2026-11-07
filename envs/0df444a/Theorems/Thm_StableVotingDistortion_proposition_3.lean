-- Prove2me | Theorems.Thm_StableVotingDistortion_proposition_3
-- name    : StableVotingDistortion.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:17.118814+00:00
-- url     : https://prove2.me/theorems/53190f84-abe2-4d78-9778-8f8cb62b93fb
-- title:
--   Proposition 3 — stationarity of $g$-stable lotteries, in multiplicative form
-- statement:
--   Let $g$ be as in Definition 3, $E$ an election, and $D$ a $g$-stable lottery. For every candidate $a$,
--   $$\Bigl(\int_0^1g(t)\,dt\Bigr)D(a)=\mathbb E_{v\sim V}\Bigl[\int_{\mathrm{rank}_v(a;D)}^{\mathrm{rank}_v(a;D)+D(a)}g(r)\,dr\Bigr].$$
--
--   Equivalently, when $\int g>0$: sampling a voter uniformly and a rank with density proportional to $g$, and outputting the candidate occupying that rank, reproduces $D$.
--
--   Differences from the source:
--   - encoding: the sampled candidate has distribution $\hat D=D_g$, for a rank with density proportional to $g$ → $(\int_0^1 g)\,D(a)=\mathbb E_v\int_{\mathrm{rank}}^{\mathrm{rank}+D(a)}g$ for every $a$; reason: this is the printed proof's display for $\hat D(a)$; a density proportional to $g$ is undefined for $g\equiv0$, which Definition 3 allows, and there both sides are $0$
--   - encoding: $D_g$ solves $\arg\min_D\max_{D^\dagger}$ → `IsGStable`: $D$ in `stdSimplex ℝ C` minimizes $H(D)=\max_{a\in C}$ over lotteries; reason: p.11: the maximum over $D^\dagger$ of a linear objective equals $H(D)$
--   - encoding: $g:[0,1]\to[0,1]$ → a function `ℝ → ℝ` with `IsActivation g`, constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Proposition 3, p.11

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_leftRank
import Definitions.Def_StableVotingDistortion_IsGStable

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Proposition 3 (stationarity).** For a `g`-stable lottery `D` and every candidate `a`,
`(∫_0^1 g) · D(a) = E_v[∫_{rank_v(a)}^{rank_v(a) + D(a)} g]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Proposition 3, p.11: "Given a g-stable lottery D_g, define a distribution D̂ as follows. Sample a
voter v ∼ V uniformly and a rank r ∼ [0, 1] with density proportional to g(r), and output the candidate
occupying rank r. Then D̂ = D_g."

**Formalization Note.** The right side is `(∫ g) · D̂(a)` by the display in the printed proof, so the
statement is `D̂ = D` when `∫ g > 0`. It is stated multiplicatively because "density proportional to g"
is undefined for `g ≡ 0`, which Definition 3 allows; there both sides are `0`. -/
theorem proposition_3 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] {g : ℝ → ℝ}
    (hg : IsActivation g) (E : Election V C) {D : C → ℝ} (hD : IsGStable g E D) (a : C) :
    (∫ t in (0 : ℝ)..1, g t) * D a =
      voterMean (fun v => ∫ r in (leftRank E D v a)..(leftRank E D v a + D a), g r) := by sorry

end StableVotingDistortion
