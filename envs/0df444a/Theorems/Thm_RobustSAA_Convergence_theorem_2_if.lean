-- Prove2me | Theorems.Thm_RobustSAA_Convergence_theorem_2_if
-- name    : RobustSAA.Convergence.theorem_2_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:48.314279+00:00
-- url     : https://prove2.me/theorems/a9b8a36a-aac4-4a76-9a08-9193bba09644
-- title:
--   Theorem 2, “if” side (p. 14; proof pp. 37–38) — a test that is not uniformly consistent fails (18)–(20) on some admissible instance
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be closed and let $N\mapsto\mathcal F_N$ be the confidence region of a test that is **not** uniformly consistent. Then there exist a data-generating distribution $F$, a decision dimension $d_x$, a decision set $X\subseteq\mathbb R^{d_x}$ and a cost $c(x;\xi)$ satisfying the standing assumptions of §1.2 and Assumptions 1, 2 and 3, for which it is not true that conditions (18)–(20) hold almost surely.
--
--   This is the necessity direction of the characterization: uniform consistency cannot be dropped, since without it some well-behaved instance fails to converge.
--
--   **Formalization Note** "Convergence fails" is the negation of "(18)–(20) hold a.s.", i.e. the set of sample paths on which one of (18)–(20) fails is not a null set. No nonemptiness of $\mathcal F_N$ is assumed. The support $\Xi$ is a general closed set, as in the statement of Theorem 2; the paper's written proof of this side treats bounded $\Xi$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 2, “if” side: statement p. 14 (first paragraph), proof §10.5 pp. 37–38

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem theorem_2_if {d : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (h𝓕 : ¬ IsUniformlyConsistent 𝓕) :
    ∃ (F : ProbabilityMeasure ↥Ξ) (dx : ℕ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ),
      Standing F X c ∧ Assumption1 X c ∧ Assumption2 F X c ∧ Assumption3 F 𝓕 X c ∧
        ¬ (∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N))) := by sorry

end RobustSAA.Convergence
