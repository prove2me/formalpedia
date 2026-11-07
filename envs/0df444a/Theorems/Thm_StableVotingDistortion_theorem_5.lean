-- Prove2me | Theorems.Thm_StableVotingDistortion_theorem_5
-- name    : StableVotingDistortion.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:02:52.649581+00:00
-- url     : https://prove2.me/theorems/9d1ca1b4-556c-4cb2-a7dc-7fe85bf3534a
-- title:
--   Theorem 5 — biased metrics are necessary and sufficient, for a fixed $a^\star$ and $\lambda\ge0$
-- statement:
--   Let $E$ be an election, $D$ a lottery, $a^\star$ a candidate and $\lambda\ge0$. Then
--   $$\mathbb E_{b\sim D}[\mathrm{cost}(b)]\le(1+2\lambda)\,\mathrm{cost}(a^\star)\quad\text{for all consistent metrics}$$
--   if and only if, for all $\rho:C\to\mathbb R_{\ge0}$ with $\rho(a^\star)=0$,
--   $$\mathbb E_{v\sim V}[L_v(D)]\le\lambda\,\mathbb E_{v\sim V}[R_v].$$
--
--   This reduces the supremum over consistent metrics to a family described by $\rho$.
--
--   Differences from the source:
--   - reading: $a^\star$ an optimal candidate, and $\lambda$ of unstated range → `aStar` is a fixed arbitrary candidate on both sides, and `0 ≤ lam`; reason: quantifying over $a^\star$ gives the printed use; $\lambda\ge0$ is required, since with one candidate, one voter at distance $1$ and $\lambda<0$, (11) holds while the bound $1\le1+2\lambda$ fails
--   - encoding: $\rho:C\to\mathbb R_{\ge0}$ → `ρ : C → ℝ` with `∀ c, 0 ≤ ρ c`; reason: the same functions
--   - encoding: a pseudometric on $V\cup C$ → `d : V ⊕ C → V ⊕ C → ℝ` with `IsPseudometric`; reason: a sum type tags voters and candidates; a voter and a candidate may be at distance $0$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 5, p.13

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsPseudometric
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_rhoV

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Theorem 5 (biased metrics are necessary and sufficient).** For a lottery `D`, a candidate `a⋆` and
`λ ≥ 0`: `E_{b∼D}[cost(b)] ≤ (1 + 2λ) cost(a⋆)` for all consistent metrics if and only if, for all
`ρ : C → ℝ≥0` with `ρ(a⋆) = 0`, `E_v[L_v(D)] ≤ λ E_v[R_v]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 5, p.13: "For a distribution D over candidates, E_{b∼D}[cost(b)] ≤ (1 + 2λ)cost(a⋆) for
all consistent metrics if and only if for all ρ : C → R≥0 such that ρ(a⋆) = 0, we have
E_{v∼V}[L_v(D)] ≤ λ E_{v∼V}[R_v]. (11)"

**Formalization Note.** `a⋆` is fixed on both sides, and quantifying over it gives the form used for an
optimal candidate. The page leaves the range of `λ` open. `λ ≥ 0` is required: with one candidate, one
voter at distance `1` and `λ < 0`, (11) holds while `1 ≤ 1 + 2λ` fails. -/
theorem theorem_5 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (aStar : C) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ d : V ⊕ C → V ⊕ C → ℝ, IsPseudometric d → Consistent E d →
        lotteryCost d D ≤ (1 + 2 * lam) * candCost d aStar) ↔
      ∀ ρ : C → ℝ, (∀ c, 0 ≤ ρ c) → ρ aStar = 0 →
        voterMean (fun v => Lv E D ρ v) ≤ lam * voterMean (fun v => Rv E ρ v) := by sorry

end StableVotingDistortion
