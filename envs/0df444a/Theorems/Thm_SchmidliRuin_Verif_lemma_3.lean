-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_lemma_3
-- name    : SchmidliRuin.Verif.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:10.147052+00:00
-- url     : https://prove2.me/theorems/e42d4a33-d9e0-48fd-b4fe-c1cec6999528
-- title:
--   Lemma 3, p. 894 — for a solution f of (3) near 0, the optimal retention is b*(u) = 1 for small u > 0
-- statement:
--   Let $c,\lambda,\mu,\sigma>0$, let $c(b)$ satisfy the standing premium assumption, and let $\nu$ be a claim law with continuous distribution function $G$, $G(0)=0$. Let $\eta>0$ and let $f$ vanish on $(-\infty,0)$, be continuous on $[0,\eta)$, twice continuously differentiable on $(0,\eta)$ with $f'>0$, $f''<0$ and $f'$ bounded there. Set
--   $$H(u,b)=-\frac{\mu^2f'(u)^2}{2\sigma^2f''(u)}+(c-c(b))f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big),\qquad Y\sim\nu,$$
--   and suppose $f$ solves (3) on $(0,\eta)$, i.e. $\sup_{b\in[0,1]}H(u,b)=0$ for $0<u<\eta$. Then there is $\varepsilon>0$ such that for every $0<u<\min(\varepsilon,\eta)$, the retention $b=1$ maximises $H(u,\cdot)$ over $[0,1]$, and every maximiser equals $1$:
--   $$b^*(u)=1\qquad(0<u<\varepsilon).$$
--
--   For small capital the optimal strategy is not to reinsure; this is used in the proof of Theorem 1 to show that ruin cannot occur by creeping.
--
--   **Formalization Note** The paper states the hypothesis as "a solution to (3) on $[0,\eta)$"; since $f''(0)$ is not defined ($f''(0+)=-\infty$, p. 895), (3) is required on $(0,\eta)$ and $u=0$ is excluded from the conclusion. Strict monotonicity and strict concavity come from the paper's restriction on p. 894 ("We therefore restrict to strictly increasing and strictly concave solutions to (1)"), and boundedness of $f'$ from the proof ("Because $f'(x)$ is bounded on $[0,\eta/2]$"). "$b^*(u)=1$" is read as: $1$ is a maximiser and it is the only one.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 894, Lemma 3

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SchmidliRuin.Verif

theorem lemma_3 (c lam mu sigma : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu)
    (hsigma : 0 < sigma) (cb : ℝ → ℝ) (hcb : ReinsPremium c cb)
    (ν : Measure ℝ) (hν : ClaimLaw ν)
    (f : ℝ → ℝ) (η : ℝ) (hη : 0 < η)
    (hf_neg : ∀ x < 0, f x = 0) (hf_cont : ContinuousOn f (Ico 0 η))
    (hf_C2 : ContDiffOn ℝ 2 f (Ioo 0 η))
    (hf_incr : ∀ u ∈ Ioo 0 η, 0 < deriv f u)
    (hf_conc : ∀ u ∈ Ioo 0 η, deriv (deriv f) u < 0)
    (hf_bdd : ∃ C : ℝ, ∀ u ∈ Ioo 0 η, deriv f u ≤ C)
    (hf_eq3 : ∀ u ∈ Ioo 0 η, IsLUB (H c lam mu sigma cb ν f u '' Icc 0 1) 0) :
    ∃ ε > 0, ∀ u ∈ Ioo 0 ε, u < η →
      IsMaxOn (H c lam mu sigma cb ν f u) (Icc 0 1) 1 ∧
      ∀ b ∈ Icc (0 : ℝ) 1, IsMaxOn (H c lam mu sigma cb ν f u) (Icc 0 1) b → b = 1 := by sorry

end SchmidliRuin.Verif
