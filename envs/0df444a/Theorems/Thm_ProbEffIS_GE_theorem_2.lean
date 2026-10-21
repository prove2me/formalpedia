-- Prove2me | Theorems.Thm_ProbEffIS_GE_theorem_2
-- name    : ProbEffIS.GE.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:49.438848+00:00
-- url     : https://prove2.me/theorems/2681c53e-b86d-4f6e-b4ef-c1d214b3c3fa
-- title:
--   Theorem 2 — most significant points minimize the rate
-- statement:
--   Under Assumptions 1 and 2, let $A=\{a_1,\ldots,a_r\}$ be a finite dominating set for the rare set $\mathcal E$. Then the minimum is attained and
--
--   $$
--   I(\mathcal E)=\min_{1\le i\le r} I(a_i).
--   $$
--
--   Thus a dominating point with smallest rate is a global rate minimizer over the rare-event set. This identifies which points the main theorem selects.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 9, Theorem 2

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- Theorem 2, p. 9: a most significant dominating point minimizes the rate. -/
theorem theorem_2 {d r : ℕ} (ν : ℝ → Measure (Rd d))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s) :
    ∃ i : Fin r, rateOn μ R = rate μ (a i) ∧
      ∀ j : Fin r, rate μ (a i) ≤ rate μ (a j) := by sorry

end ProbEffIS.GE
