-- Prove2me | Theorems.Thm_StableVotingDistortion_lemma_8
-- name    : StableVotingDistortion.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:11.786625+00:00
-- url     : https://prove2.me/theorems/ccaca65d-568d-40e8-b9c6-a4dd7fc4d5ae
-- title:
--   Lemma 8 (Verifier Lemma) — $\phi,\beta,c$ satisfying (26), (37), (38) give distortion at most $1+2\lambda$
-- statement:
--   Let $\lambda\in(0,1)$, let $\phi$ satisfy (26) with $\phi(r)+r$ nonincreasing on $[\lambda,1]$, and let $\beta:(0,1)\to\mathbb R_{\ge0}$ and $c:(0,1)\times[0,\lambda)\to\mathbb R_{\ge0}$ satisfy (37) and (38) for every $p\in(0,1)$ and $x\in[0,\lambda)$. Then in any election, every $g_\phi$-stable lottery has distortion at most $1+2\lambda$.
--
--   The hypotheses mention no election, which makes this a checkable analytic criterion.
--
--   Differences from the source:
--   - reading: distortion at most $B$, as the ratio $\mathrm{cost}_d(D)/\min_a\mathrm{cost}_d(a)$ → `HasDistortionAtMost`: $\mathrm{cost}_d(D)\le B\,\mathrm{cost}_d(a)$ for all consistent $d$ and all candidates $a$; reason: the same for a positive minimum; it avoids division by zero, and with a zero minimum it forces $\mathrm{cost}_d(D)=0$
--   - reading: $g(\mathrm{rank}_v(a;D))$, with $\mathrm{rank}_v$ overloaded on p.8 → `activation`: the average of $g$ over $a$'s interval if $D(a)\neq0$, and $g$ at the left boundary if $D(a)=0$; reason: p.8 makes the attacker's rank a uniformly random point of its interval, p.22 gives the zero-mass value, and the proof of Theorem 4 needs a uniformly random rank under $a\sim D$
--   - encoding: $D_g$ solves $\arg\min_D\max_{D^\dagger}$ → `IsGStable`: $D$ in `stdSimplex ℝ C` minimizes $H(D)=\max_{a\in C}$ over lotteries; reason: p.11: the maximum over $D^\dagger$ of a linear objective equals $H(D)$
--   - encoding: a pseudometric on $V\cup C$ → `d : V ⊕ C → V ⊕ C → ℝ` with `IsPseudometric`; reason: a sum type tags voters and candidates; a voter and a candidate may be at distance $0$
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $\beta:(0,1)\to\mathbb R_{\ge0}$, $c:(0,1)\times[0,\lambda)\to\mathbb R_{\ge0}$ → total functions constrained only on those domains; reason: Lean functions are total; only printed arguments are used
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 8, p.31

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_VerifierHypotheses

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Lemma 8 (Verifier Lemma).** If `λ, ϕ, β, c` satisfy the hypotheses of the lemma, then in any election
every `g_ϕ`-stable lottery has distortion at most `1 + 2λ`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 8, p.31: "Let ϕ satisfy Equation (26) and let ϕ(r) + r be nonincreasing on [λ, 1]. Let
β : (0, 1) → R≥0 and c : (0, 1) × [0, λ) → R≥0 satisfy Equations (37) and (38) for every p ∈ (0, 1) and
x ∈ [0, λ). Then every g_ϕ-stable lottery has distortion at most 1 + 2λ." -/
theorem lemma_8 {lam : ℝ} {ϕ β : ℝ → ℝ} {c : ℝ → ℝ → ℝ} (h : VerifierHypotheses lam ϕ β c)
    {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) {D : C → ℝ}
    (hD : IsGStable (gPhi ϕ) E D) : HasDistortionAtMost E D (1 + 2 * lam) := by sorry

end StableVotingDistortion
