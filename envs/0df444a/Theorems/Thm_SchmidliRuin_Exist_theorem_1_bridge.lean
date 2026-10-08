-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_theorem_1_bridge
-- name    : SchmidliRuin.Exist.theorem_1_bridge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:45.57402+00:00
-- url     : https://prove2.me/theorems/2fdf7bd7-b653-41a6-9061-8e609ec72882
-- title:
--   Theorem 1 (second sentence), p. 896 — for a decreasing solution g of (5), f(x) = 1 + ∫₀ˣ g solves the HJB equation (1)
-- statement:
--   Assume the standing assumptions. Let $g$ be a decreasing solution of (5) on $[0,\infty)$, and let
--   $$
--   f(x)=1+\int_0^xg(z)\,dz\quad(x\ge0),\qquad f(x)=0\quad(x<0).
--   $$
--   Then the following hold.
--
--   1. $f$ is strictly increasing and continuous on $[0,\infty)$.
--   2. $f$ is twice continuously differentiable on $(0,\infty)$.
--   3. $f$ solves the Hamilton–Jacobi–Bellman equation (1),
--   $$
--   \sup_{b\in[0,1]}\sup_{A\ge0}\Big[\tfrac12\sigma^2A^2f''(u)+\big(c-c(b)+\mu A\big)f'(u)+\lambda\big(\mathbb E[f(u-bY)]-f(u)\big)\Big]=0 ,
--   $$
--   at every $u>0$, and at $u=0$ in its boundary form $\sup_{b\in[0,1]}\big[(c-c(b))f'(0)+\lambda(\mathbb E[f(-bY)]-f(0))\big]=0$.
--
--   This links the integral equation (5) to the control problem. By Theorem 1, a solution of (1) of this kind is, after normalisation, the maximal survival probability. The existence part of Theorem 2 therefore gives a solution of the optimisation problem.
--
--   **Formalization Note.** "Twice continuously differentiable" is read on $(0,\infty)$: the paper shows $f''(0+)=-\infty$ (p. 895). At $u=0$ the equation is taken in the form the convention $f''(0+)=-\infty$ gives, with the right derivative $f'(0)$. Every supremum is a least upper bound. $\mathbb E[f(u-bY)]$ uses $f=0$ on $(-\infty,0)$, as the paper does.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 896, Theorem 1 (second sentence)

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- Theorem 1, second sentence (Schmidli 2002, p. 896): if `g` is a decreasing solution of (5),
then `f(x) = 1 + ∫_0^x g(z) dz` (and `f = 0` on `(-∞, 0)`) is a strictly increasing function,
twice continuously differentiable on `(0, ∞)`, solving the HJB equation (1) on `[0, ∞)`. -/
theorem theorem_1_bridge
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (g : ℝ → ℝ)
    (hg_anti : AntitoneOn g (Ici 0))
    (hg : SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    (f : ℝ → ℝ) (hf : ∀ x, f x = if x < 0 then 0 else 1 + ∫ z in (0 : ℝ)..x, g z) :
    StrictMonoOn f (Ici 0) ∧ ContinuousOn f (Ici 0) ∧ ContDiffOn ℝ 2 f (Ioi 0) ∧
      SolvesHJBAtZero c lam cb ν f ∧ ∀ u > 0, SchmidliRuin.Verif.SolvesHJB c lam mu sigma cb ν f u := by sorry

end SchmidliRuin.Exist
