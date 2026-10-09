-- Prove2me | Theorems.Thm_RobustSAA_Convergence_theorem_2
-- name    : RobustSAA.Convergence.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:26.294501+00:00
-- url     : https://prove2.me/theorems/2cdb1ac2-f00a-4834-9baf-4cdf5308866c
-- title:
--   Theorem 2, p. 13 — 𝓕_N is the confidence region of a uniformly consistent test iff Assumptions 1–3 imply (18)–(20) a.s.
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed and let $N\mapsto\mathcal F_N$ be a DUS map whose sets $\mathcal F_N(\xi^1,\dots,\xi^N)$ are all nonempty. Then $\mathcal F_N$ is the confidence region of a uniformly consistent test **if and only if** the following holds: for every data-generating distribution $F$ on $\Xi$, every decision set $X\subseteq\mathbb R^{d_x}$ and every cost $c(x;\xi)$ satisfying the standing assumptions of §1.2 and Assumptions 1, 2 and 3, almost surely
--
--   1. (18) $\mathcal C(x;\mathcal F_N)\to\mathbb E_F[c(x;\xi)]$ uniformly over every compact subset of $X$, where $\mathcal C(x;\mathcal F_N)=\sup_{F_0\in\mathcal F_N}\mathbb E_{F_0}[c(x;\xi)]$;
--   2. (19) $\displaystyle\min_{x\in X}\mathcal C(x;\mathcal F_N)\to\min_{x\in X}\mathbb E_F[c(x;\xi)]$;
--   3. (20) every sequence $x_N\in\arg\min_{x\in X}\mathcal C(x;\mathcal F_N)$ has at least one limit point, and all of its limit points lie in $\arg\min_{x\in X}\mathbb E_F[c(x;\xi)]$.
--
--   The theorem says that the convergence of Robust SAA, and of every data-driven distributionally robust formulation whose uncertainty set is a confidence region, is governed by one statistical property of the underlying goodness-of-fit test.
--
--   **Formalization Note** Every DUS is the confidence region of the test "reject $F_0$ iff $F_0\notin\mathcal F_N$", so the left side is uniform consistency of the DUS map. Nonemptiness of every $\mathcal F_N$ is added (needed for the "only if" side, see that milestone). Expectations over members of $\mathcal F_N$ are $+\infty$ when not integrable; minima are infima in the extended reals; (20) concerns sequences that are minimizers for all large $N$. Continuity of $c(x;\cdot)$ and of $\phi$, and openness of $D$ in Assumption 2b, are added to the assumptions as described in the setting file.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 2, p. 13; proof §10.5, pp. 36–38

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem theorem_2 {d : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (hne : ∀ (N : ℕ) (s : Fin N → ↥Ξ), (𝓕 N s).Nonempty) :
    IsUniformlyConsistent 𝓕 ↔
      ∀ (F : ProbabilityMeasure ↥Ξ) (dx : ℕ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ),
        Standing F X c → Assumption1 X c → Assumption2 F X c → Assumption3 F 𝓕 X c →
          ∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N)) := by sorry

end RobustSAA.Convergence
