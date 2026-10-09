-- Prove2me | Theorems.Thm_RobustSAA_Convergence_theorem_3
-- name    : RobustSAA.Convergence.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:35.192135+00:00
-- url     : https://prove2.me/theorems/5009b405-92b0-4f0d-9787-60a3d90d863a
-- title:
--   Theorem 3, p. 14 — with the empirical distribution in 𝓕_N and a c-consistent test, (18)–(20) hold a.s. (Assumption 2 added)
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed, let the data be i.i.d. from $F$, and let $X$ and $c(x;\xi)$ satisfy the standing assumptions of §1.2 and Assumptions 1, 2 and 3. Suppose that for every $N\ge1$ and every sample, $\mathcal F_N$ contains the empirical distribution $\hat F_N=\frac1N\sum_{i=1}^N\delta_{\xi^i}$, and that $\mathcal F_N$ is the confidence region of a $c$-consistent test. Then, almost surely, conditions (18)–(20) hold:
--   $$\mathcal C(x;\mathcal F_N)\to\mathbb E_F[c(x;\xi)]\ \text{uniformly on compacts of }X,\quad \min_{X}\mathcal C(\cdot;\mathcal F_N)\to\min_X\mathbb E_F[c(\cdot;\xi)],$$
--   and every sequence of minimizers of $\mathcal C(\cdot;\mathcal F_N)$ has a limit point, all of whose limit points minimize $\mathbb E_F[c(\cdot;\xi)]$.
--
--   This result explains why a DRO can converge for a given cost even when its test is not consistent: only consistency with respect to the expected cost is needed.
--
--   **Formalization Note** Assumption 2 is added to the page's hypotheses (with the standing assumptions): the paper's proof is shared with the "only if" side of Theorem 2 and uses it ("If $X$ is compact (Assumption 2a) … Suppose $X$ is not compact (Assumption 2b)", p. 37); without it (19)–(20) fail for $c\equiv0$ on $X=\mathbb R$. "Contains the empirical distribution" means some member of $\mathcal F_N$ equals $\hat F_N$ as a measure, for every $N\ge1$. $c$-consistency is Definition 5 with extended-real expectations.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 3, p. 14; proof §10.5, p. 37

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Convergence_Consistency

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem theorem_3 {d dx : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (hS : Standing F X c) (hA1 : Assumption1 X c) (hA2 : Assumption2 F X c)
    (hA3 : Assumption3 F 𝓕 X c)
    (hemp : ∀ (N : ℕ), 0 < N → ∀ s : Fin N → ↥Ξ,
      ∃ G ∈ 𝓕 N s, (G : Measure ↥Ξ) = empiricalMeasure s)
    (hc : IsCConsistent X c 𝓕) :
    ∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N)) := by sorry

end RobustSAA.Convergence
