-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_theorem_1_uniqueness
-- name    : SchmidliRuin.Exist.theorem_1_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:02.274813+00:00
-- url     : https://prove2.me/theorems/edcf23b0-a54b-4768-becc-4498af1cdb47
-- title:
--   Theorem 1 (last sentence), p. 896 — at most one strictly increasing C² solution of (1) with f(0) = 1
-- statement:
--   Assume the standing assumptions. Let $f_1,f_2:\mathbb R\to\mathbb R$ each satisfy the following.
--
--   1. $f_i(x)=0$ for $x<0$, $f_i\ge0$ on $[0,\infty)$, and $f_i(0)=1$.
--   2. $f_i$ is strictly increasing and continuous on $[0,\infty)$.
--   3. $f_i$ is twice continuously differentiable on $(0,\infty)$.
--   4. $f_i$ solves the Hamilton–Jacobi–Bellman equation (1) at every $u>0$,
--   $$
--   \sup_{b\in[0,1]}\sup_{A\ge0}\Big[\tfrac12\sigma^2A^2f''(u)+\big(c-c(b)+\mu A\big)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big)\Big]=0 ,
--   $$
--   and at $u=0$ in its boundary form $\sup_{b\in[0,1]}\big[(c-c(b))f'(0)+\lambda(\mathbb E[f(-bY)]-f(0))\big]=0$.
--
--   Then $f_1=f_2$ on $[0,\infty)$.
--
--   Combined with the bridge statement (Theorem 1, second sentence), this gives the uniqueness part of Theorem 2. Two strictly decreasing solutions of (5) produce two such solutions of (1) with $f(0)=1$.
--
--   **Formalization Note.** The statement is pure analysis, although the paper derives it from the verification argument. "Twice continuously differentiable" is read on $(0,\infty)$, since $f''(0+)=-\infty$ (p. 895). The paper's $f:\mathbb R_+\to\mathbb R_+$ solving (1) on $\mathbb R_+$ includes $u=0$, where the equation takes the boundary form above. Every supremum is a least upper bound.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 896, Theorem 1 (last sentence)

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- Theorem 1, last sentence (Schmidli 2002, p. 896): there is at most one strictly increasing,
twice continuously differentiable solution `f : ℝ₊ → ℝ₊` of (1) with `f(0) = 1`. -/
theorem theorem_1_uniqueness
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (f₁ f₂ : ℝ → ℝ)
    (h₁_neg : ∀ x < 0, f₁ x = 0) (h₁_nonneg : ∀ x ≥ 0, 0 ≤ f₁ x)
    (h₁_mono : StrictMonoOn f₁ (Ici 0)) (h₁_cont : ContinuousOn f₁ (Ici 0))
    (h₁_C2 : ContDiffOn ℝ 2 f₁ (Ioi 0))
    (h₁_zero : SolvesHJBAtZero c lam cb ν f₁)
    (h₁_hjb : ∀ u > 0, SchmidliRuin.Verif.SolvesHJB c lam mu sigma cb ν f₁ u) (h₁_init : f₁ 0 = 1)
    (h₂_neg : ∀ x < 0, f₂ x = 0) (h₂_nonneg : ∀ x ≥ 0, 0 ≤ f₂ x)
    (h₂_mono : StrictMonoOn f₂ (Ici 0)) (h₂_cont : ContinuousOn f₂ (Ici 0))
    (h₂_C2 : ContDiffOn ℝ 2 f₂ (Ioi 0))
    (h₂_zero : SolvesHJBAtZero c lam cb ν f₂)
    (h₂_hjb : ∀ u > 0, SchmidliRuin.Verif.SolvesHJB c lam mu sigma cb ν f₂ u) (h₂_init : f₂ 0 = 1) :
    EqOn f₁ f₂ (Ici 0) := by sorry

end SchmidliRuin.Exist
