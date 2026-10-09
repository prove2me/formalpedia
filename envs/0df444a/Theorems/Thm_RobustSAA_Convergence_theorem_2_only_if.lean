-- Prove2me | Theorems.Thm_RobustSAA_Convergence_theorem_2_only_if
-- name    : RobustSAA.Convergence.theorem_2_only_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:50.395402+00:00
-- url     : https://prove2.me/theorems/9fc87088-7909-4469-843e-48f7fe02553b
-- title:
--   Theorem 2, “only if” side (p. 14; proof p. 37) — a uniformly consistent test gives (18)–(20) a.s. under Assumptions 1–3
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed and let $N\mapsto\mathcal F_N$ be a DUS map whose sets are all nonempty and which is the confidence region of a uniformly consistent test. Then for every data-generating distribution $F$, every decision dimension $d_x$, every decision set $X\subseteq\mathbb R^{d_x}$ and every cost $c(x;\xi)$ satisfying the standing assumptions of §1.2 and Assumptions 1, 2 and 3, almost surely:
--
--   1. (18) $\mathcal C(x;\mathcal F_N)\to\mathbb E_F[c(x;\xi)]$ uniformly over every compact subset of $X$;
--   2. (19) $\displaystyle\inf_{x\in X}\mathcal C(x;\mathcal F_N)\to\inf_{x\in X}\mathbb E_F[c(x;\xi)]$;
--   3. (20) every sequence $x_N\in\arg\min_{x\in X}\mathcal C(x;\mathcal F_N)$ has at least one limit point, and all of its limit points lie in $\arg\min_{x\in X}\mathbb E_F[c(x;\xi)]$.
--
--   This is the sufficiency direction of the paper's characterization: using a uniformly consistent test in Robust SAA guarantees convergence of the objective, the optimal value and the optimal solutions.
--
--   **Formalization Note** Nonemptiness of every $\mathcal F_N$ is added: with $\mathcal F_N=\emptyset$ the worst case is $-\infty$ and (18) fails, while uniform consistency holds vacuously; the paper's proof uses it ("By definition of supremum, $\exists F_N\in\mathcal F_N$", p. 37). The added continuity and openness conditions inside the standing assumptions and Assumptions 2–3 are those of the setting file. Infima are in the extended reals and (20) concerns sequences that are minimizers for all large $N$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 2, “only if” side: statement p. 14 (first paragraph), proof §10.5 p. 37

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem theorem_2_only_if {d : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (hne : ∀ (N : ℕ) (s : Fin N → ↥Ξ), (𝓕 N s).Nonempty)
    (h𝓕 : IsUniformlyConsistent 𝓕) :
    ∀ (F : ProbabilityMeasure ↥Ξ) (dx : ℕ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ),
      Standing F X c → Assumption1 X c → Assumption2 F X c → Assumption3 F 𝓕 X c →
        ∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N)) := by sorry

end RobustSAA.Convergence
