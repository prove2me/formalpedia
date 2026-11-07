-- Prove2me | Theorems.Thm_StableVotingDistortion_lemma_14_i
-- name    : StableVotingDistortion.lemma_14_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:03:04.641226+00:00
-- url     : https://prove2.me/theorems/768bed49-1ab3-444e-a3a0-a5c37974fb5c
-- title:
--   Lemma 14(i) — small masses: (37), (38) for $p\in(0,p_0]$ with $\beta=\beta_0$
-- statement:
--   Let $\lambda\in(0,1)$, let $\phi$ satisfy (26) with $\phi(r)+r$ nonincreasing on $[\lambda,1]$, and let $0<p_0<\lambda$. Let $\beta_0>0$ satisfy
--   $$\beta_0\phi(p_0)\ge1,\qquad p_0(1+\beta_0(1+\phi(0)))\le\lambda,$$
--   $$p_0[1-\beta_0(\phi(p_0)-\phi(x))]\le\sigma(x)\quad\text{for }0\le x\le\lambda.$$
--   Then (37) and (38) hold for every $p\in(0,p_0]$ with $\beta(p)=\beta_0$ and $c(p,x)=((1+\beta_0p)\phi(x)-(\lambda-x))_+$.
--
--   Differences from the source:
--   - reading: "$\phi$ satisfy the hypotheses of Lemma 8", and $0<p_0<\lambda<p_1<1$ → the hypotheses on $\phi$ only, and $0<p_0<\lambda$; reason: $\beta$ and $c$ are what the lemma produces, and $p_1$ plays no part in (i)
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 14(i), p.44

import Mathlib
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_VerifierHypotheses

set_option autoImplicit false

namespace StableVotingDistortion

/-- **Lemma 14(i) (small masses).** Let `ϕ` satisfy (26) with `ϕ(r) + r` nonincreasing on `[λ, 1]`, and let
`0 < p₀ < λ`. If `β₀ > 0` satisfies (45), then (37) and (38) hold for every `p ∈ (0, p₀]` with `β(p) = β₀` and
`c(p, x) = ((1 + β₀ p) ϕ(x) − (λ − x))₊`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 14(i), p.44: "Let ϕ satisfy the hypotheses of Lemma 8, and let 0 < p_0 < λ < p_1 < 1. (i) Let
β_0 > 0 satisfy β_0 ϕ(p_0) ≥ 1, p_0 (1 + β_0(1 + ϕ(0))) ≤ λ, p_0 [1 − β_0 (ϕ(p_0) − ϕ(x))] ≤ σ(x) for 0 ≤ x ≤ λ.
(45) Then Equations (37) and (38) hold for every p ∈ (0, p_0] with β(p) = β_0 and
c(p, x) = ((1 + β_0 p)ϕ(x) − (λ − x))_+."

**Formalization Note.** "The hypotheses of Lemma 8" are those on `ϕ`: `β` and `c` are what this lemma
produces. `p₁` of the page's opening sentence plays no part in (i) and is not a binder. -/
theorem lemma_14_i {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p0 : ℝ} (hp0 : 0 < p0) (hp0lam : p0 < lam) {β0 : ℝ} (hβ0 : 0 < β0)
    (h45a : 1 ≤ β0 * ϕ p0) (h45b : p0 * (1 + β0 * (1 + ϕ 0)) ≤ lam)
    (h45c : ∀ x ∈ Set.Icc 0 lam, p0 * (1 - β0 * (ϕ p0 - ϕ x)) ≤ sigma lam ϕ x) :
    ∀ p ∈ Set.Ioc 0 p0,
      Eq37 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p ∧
        Eq38 lam ϕ (fun _ => β0) (fun p x => max ((1 + β0 * p) * ϕ x - (lam - x)) 0) p := by sorry

end StableVotingDistortion
