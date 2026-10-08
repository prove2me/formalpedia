-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_lemma_3
-- name    : SchmidliRuin.Exist.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:08.643982+00:00
-- url     : https://prove2.me/theorems/f3948f03-bc69-41a6-ad4e-5ed467f8c6d6
-- title:
--   Lemma 3, p. 894 — for a solution f of (3) on [0, η), the optimal retention level is b*(u) = 1 for small u
-- statement:
--   Assume the standing assumptions on $c,\lambda,\mu,\sigma$, on the reinsurance premium $c(b)$ and on the claim law. Let $\eta>0$, and let $f:\mathbb R\to\mathbb R$ satisfy the following.
--
--   1. $f(u)=0$ for $u<0$, and $f$ is continuous on $[0,\eta)$.
--   2. $f$ is twice continuously differentiable on $(0,\eta)$, with $f'>0$ and $f''<0$ there (the paper's restriction to strictly increasing, strictly concave solutions, p. 894).
--   3. $f$ solves (3) on $[0,\eta)$: $\sup_{b\in[0,1]}H(u,b)=0$ for every $u\in(0,\eta)$, where
--   $$
--   H(u,b)=-\frac{\mu^2f'(u)^2}{2\sigma^2f''(u)}+\big(c-c(b)\big)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big),
--   $$
--   and at $u=0$ the boundary form $\sup_{b\in[0,1]}\big[(c-c(b))f'(0)+\lambda(\mathbb E[f(-bY)]-f(0))\big]=0$ holds, with $f'(0)$ the right derivative.
--
--   Then there is $\varepsilon>0$ such that for every $u\in(0,\varepsilon)$ with $u<\eta$, $b=1$ maximises $H(u,\cdot)$ over $[0,1]$ and is its only maximiser: $b^*(u)=1$.
--
--   In words, for small capital it is optimal not to reinsure. Near $0$, equation (3) is therefore the equation without reinsurance treated by Hipp and Plum (2000), and this is what reduces local existence (Lemma 4) to that case.
--
--   **Formalization Note.** "$b^*(u)=1$" is read as "$1$ is a maximiser and every maximiser equals $1$", because the paper says $b^*$ is not necessarily unique (p. 894). The conclusion is stated for $u>0$, where $f''(u)$ exists. The point $u=0$ is part of the hypothesis "solution on $[0,\eta)$". Under the paper's convention $f''(0+)=-\infty$ (p. 895) the investment term vanishes there, and the proof's "Note that $b(0)=1$" is that boundary equation. Without the boundary equation the statement fails: a premium $c(b)$ that is flat near $b=0$ admits local solutions of (3) on $(0,\eta)$ with $b^*\equiv0$. The proof's "$f'(x)$ is bounded on $[0,\eta/2]$" follows from the right-differentiability at $0$ and the monotonicity of $f'$, so it is not assumed separately.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 894, Lemma 3

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- Lemma 3 (Schmidli 2002, p. 894): if `f` solves (3) on `[0, η)`, then the maximiser
`b*(u)` of `H(u, ·)` over `[0, 1]` is `1` for all small `u > 0`. -/
theorem lemma_3
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (f : ℝ → ℝ) (η : ℝ) (hη : 0 < η)
    (hf_neg : ∀ x < 0, f x = 0)
    (hf_cont : ContinuousOn f (Ico 0 η))
    (hf_C2 : ContDiffOn ℝ 2 f (Ioo 0 η))
    (hf'_pos : ∀ u ∈ Ioo 0 η, 0 < deriv f u)
    (hf''_neg : ∀ u ∈ Ioo 0 η, deriv (deriv f) u < 0)
    (hf_zero : SolvesHJBAtZero c lam cb ν f)
    (hf_eq3 : ∀ u ∈ Ioo 0 η, SolvesEq3At c lam mu sigma cb ν f u) :
    ∃ ε > 0, ∀ u ∈ Ioo 0 ε, u < η →
      IsMaxOn (SchmidliRuin.Verif.H c lam mu sigma cb ν f u) (Icc 0 1) 1 ∧
      ∀ b ∈ Icc (0 : ℝ) 1, IsMaxOn (SchmidliRuin.Verif.H c lam mu sigma cb ν f u) (Icc 0 1) b → b = 1 := by sorry

end SchmidliRuin.Exist
