-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_lemma_5
-- name    : SchmidliRuin.Exist.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:56.84748+00:00
-- url     : https://prove2.me/theorems/34e98711-7c5e-4795-9c15-5eb527f9d0eb
-- title:
--   Lemma 5, p. 899 — a decreasing solution of (5) on [0, u₀) with (6) on (0, u₀) extends to [0, u₀], and (6) holds at u₀
-- statement:
--   Assume the standing assumptions and that $G$ has a bounded density. Let $u_0>0$, and let $g$ be a decreasing solution of (5) on $[0,u_0)$ such that condition (6) holds for every $u\in(0,u_0)$. Then there is $\tilde g$ with $\tilde g=g$ on $[0,u_0)$ such that $\tilde g$ solves (5) on $[0,u_0]$ and (6) holds at $u=u_0$:
--   $$
--   \inf_{b\in[0,1]}\lambda\Big(1-G(u_0/b)+\int_0^{u_0}\big(1-G((u_0-z)/b)\big)\tilde g(z)\,dz\Big)-\big(c-c(b)\big)\tilde g(u_0)>0 .
--   $$
--
--   Lemma 5 is the closure step of the continuation argument: a solution cannot stop at a finite endpoint because (6) degenerates there.
--
--   **Formalization Note.** The value $\tilde g(u_0)$ is forced by (5); the paper takes it to be the left limit of $g$. "Decreasing" is non-increasing, as printed. The paper's proof normalises $\lambda=c=1$; the statement keeps general $\lambda$ and $c$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 899, Lemma 5

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- Lemma 5 (Schmidli 2002, p. 899): a decreasing solution of (5) on `[0, u₀)` satisfying (6) on
`(0, u₀)` extends to `[0, u₀]`, and (6) holds at `u₀`. -/
theorem lemma_5
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (hdens : HasBoundedDensity ν)
    (u₀ : ℝ) (hu₀ : 0 < u₀) (g : ℝ → ℝ)
    (hg_anti : AntitoneOn g (Ico 0 u₀))
    (hg : SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Ico 0 u₀))
    (hg6 : ∀ u ∈ Ioo 0 u₀, Cond6 c lam cb ν g u) :
    ∃ g' : ℝ → ℝ, EqOn g' g (Ico 0 u₀) ∧ SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g' (Icc 0 u₀) ∧
      Cond6 c lam cb ν g' u₀ := by sorry

end SchmidliRuin.Exist
