-- Prove2me | Theorems.Thm_StableVotingDistortion_eq_33
-- name    : StableVotingDistortion.eq_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:40.947831+00:00
-- url     : https://prove2.me/theorems/e37c0c07-d441-4651-ad5e-a5744c8dcb8d
-- title:
--   Equations (32)–(33) — the offset slice does not lower the mean
-- statement:
--   Let $\lambda\in(0,1)$, $\phi$ satisfy (26), $D$ be a $g_\phi$-stable lottery, $\rho\ge0$ with $\rho(a^\star)=0$, and $t\ge0$. Assume $A>0$ and $0<p_t<1$, and let $\beta(p)\ge0$ and $c(p,x)\ge0$ for $p\in(0,1)$ and $x\in[0,\lambda)$. With $\tilde q_v(t)$ defined by (32),
--   $$\mathbb E_v[q_v(t)]\le\mathbb E_v[\tilde q_v(t)].$$
--
--   The cases $p_t\in\{0,1\}$ and $A=0$ are treated separately on pp.30–31 and are part of Lemma 8, not of this item.
--
--   Differences from the source:
--   - encoding: $\beta:(0,1)\to\mathbb R_{\ge0}$, $c:(0,1)\times[0,\lambda)\to\mathbb R_{\ge0}$ → total functions constrained only on those domains; reason: Lean functions are total; only printed arguments are used
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (32), (33), p.29

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices
import Definitions.Def_StableVotingDistortion_offset

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Equations (32)–(33).** For a `g_ϕ`-stable lottery under (26), `ρ ≥ 0` with `ρ(a⋆) = 0`, `t ≥ 0`, `A > 0`,
`0 < p_t < 1`, `β ≥ 0` on `(0, 1)` and `c ≥ 0` on `(0, 1) × [0, λ)`, the offset slice of (32) satisfies
`E_v[q_v(t)] ≤ E_v[q̃_v(t)]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (32), (33), p.29: "let A = E_v[1{s_v<λ}ϕ(s_v)] and assume for now that A > 0 and
0 < p_t < 1. Given β(p) ≥ 0 and c(p, x) ≥ 0 for p ∈ (0, 1) and x < λ, we define q̃_v(t) = q_v(t) + β(p_t)k_v(t) +
{c(p_t, s_v), s_v < λ; ϕ(s_v) c̄(p_t), s_v ≥ λ}, c̄(p) = E_v[1{s_v<λ}c(p, s_v)]/A. (32)" and "Consequently,
E_v[q_v(t)] ≤ E_v[q̃_v(t)]. (33)" -/
theorem eq_33 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ β : ℝ → ℝ} {c : ℝ → ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {D ρ : C → ℝ} (hD : IsGStable (gPhi ϕ) E D) (hρ : ∀ b, 0 ≤ ρ b) {aStar : C} (hstar : ρ aStar = 0)
    {t : ℝ} (ht : 0 ≤ t) (hA : 0 < Aval lam ϕ E D aStar)
    (hpt : pt D ρ t ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ β p)
    (hc : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ico 0 lam, 0 ≤ c p x) :
    voterMean (fun v => qv E D ρ v t) ≤ voterMean (fun v => qTilde lam ϕ β c E D ρ aStar v t) := by sorry

end StableVotingDistortion
