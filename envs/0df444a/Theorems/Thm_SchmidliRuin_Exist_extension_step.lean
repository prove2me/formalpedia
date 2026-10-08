-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_extension_step
-- name    : SchmidliRuin.Exist.extension_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:32.785163+00:00
-- url     : https://prove2.me/theorems/db50a155-2bf0-491d-b766-e537a9fcd9c3
-- title:
--   §4, proof of Theorem 2, p. 901 — a solution of (5) with (6) on (0, u₀] continues to [0, u₀ + η) with (6)
-- statement:
--   Assume the standing assumptions and that $G$ has a bounded density. Let $u_0>0$, and let $g$ solve (5) on $[0,u_0]$ with condition (6) for every $u\in(0,u_0]$. Then there are $\eta>0$ and $\tilde g$ such that the following hold.
--
--   1. $\tilde g=g$ on $[0,u_0]$.
--   2. $\tilde g$ solves (5) on $[0,u_0+\eta)$.
--   3. Condition (6) holds for $\tilde g$ at every $u\in(0,u_0+\eta)$.
--
--   This is the local continuation step in the proof of Theorem 2. Together with Lemma 5, it shows that the maximal interval on which (5) and (6) hold is all of $[0,\infty)$.
--
--   **Formalization Note.** The statement is the conclusion the page draws ("Thus there is a solution $g(x)$ to (5) on $(0,u_0+\eta)$ such that (6) holds"). The contraction estimate for the operator $\mathcal V$ of (7) that precedes it depends on constants that are not pinned on the page, so it is not stated. The paper writes the interval open at $0$; (5) at $u=0$ only says $g(0)=\lambda/c$, so $[0,u_0+\eta)$ is the same claim. Here $\lambda$ and $c$ are general, while the page normalises $\lambda=c=1$.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), pp. 900–901, §4, proof of Theorem 2 (operator (7) and the final paragraph)

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- §4, proof of Theorem 2, p. 901: a solution of (5) on `[0, u₀]` satisfying (6) on `(0, u₀]`
extends to a solution of (5) on `[0, u₀ + η)` satisfying (6) there, for some `η > 0`. -/
theorem extension_step
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (hdens : HasBoundedDensity ν)
    (u₀ : ℝ) (hu₀ : 0 < u₀) (g : ℝ → ℝ)
    (hg : SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Icc 0 u₀))
    (hg6 : ∀ u ∈ Ioc 0 u₀, Cond6 c lam cb ν g u) :
    ∃ η > 0, ∃ g' : ℝ → ℝ, EqOn g' g (Icc 0 u₀) ∧
      SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g' (Ico 0 (u₀ + η)) ∧
      ∀ u ∈ Ioo 0 (u₀ + η), Cond6 c lam cb ν g' u := by sorry

end SchmidliRuin.Exist
