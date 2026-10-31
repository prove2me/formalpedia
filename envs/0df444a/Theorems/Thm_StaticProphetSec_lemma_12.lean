-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_12
-- name    : StaticProphetSec.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:11.680807+00:00
-- url     : https://prove2.me/theorems/99c61224-e3c0-4208-9a1d-09eb80e0760c
-- title:
--   Lemma 12 — structure of solutions of problem (37)
-- statement:
--   Suppose problem (37) is feasible. Then:
--
--   1. Any feasible solution in the interior $(0,1)^2$ with $p_1\ne p_2$ is suboptimal, unless all feasible solutions have the same objective value.
--   2. If $A_2=0$, $A_1\ne0$ and $B_2<0$, then any feasible solution with $p_1\ne p_2$ is suboptimal.
--   3. If $A_2\ne0$, $A_1/A_2\le-1$ and $B_1-B_2A_1/A_2<0$, then any feasible solution with $p_1\ne p_2$ is suboptimal.
--
--   This is the two-variable step of Lemma 2: reoptimizing a pair of means while holding the others fixed.
--
--   Differences from the source:
--
--   - encoding: "suboptimal", "any solution" → some feasible point has a strictly smaller objective; "any solution" is any feasible point; reason: the standard meaning of the terms for problem (37)
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 12, p.34

import Mathlib
import Definitions.Def_StaticProphetSec_suboptimal37

namespace StaticProphetSec

/-- Lemma 12 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 12, p.34), all three statements, for
problem (37): if the problem is feasible, then (1) a feasible interior point with `p1 ≠ p2` is
suboptimal unless all feasible points have the same objective value; (2) if `A2 = 0`, `A1 ≠ 0`
and `B2 < 0`, every feasible point with `p1 ≠ p2` is suboptimal; (3) if `A2 ≠ 0`, `A1/A2 ≤ -1`
and `B1 - B2 A1/A2 < 0`, every feasible point with `p1 ≠ p2` is suboptimal. -/
theorem lemma_12 (A0 A1 A2 B0 B1 B2 φ : ℝ)
    (hfeas : ∃ p1 p2 : ℝ, feasible37 A0 A1 A2 φ p1 p2) :
    (∀ p1 p2 : ℝ, feasible37 A0 A1 A2 φ p1 p2 → 0 < p1 → p1 < 1 → 0 < p2 → p2 < 1 → p1 ≠ p2 →
      (¬ ∀ a1 a2 b1 b2 : ℝ, feasible37 A0 A1 A2 φ a1 a2 → feasible37 A0 A1 A2 φ b1 b2 →
          objective37 B0 B1 B2 a1 a2 = objective37 B0 B1 B2 b1 b2) →
        suboptimal37 A0 A1 A2 B0 B1 B2 φ p1 p2) ∧
    (A2 = 0 → A1 ≠ 0 → B2 < 0 →
      ∀ p1 p2 : ℝ, feasible37 A0 A1 A2 φ p1 p2 → p1 ≠ p2 →
        suboptimal37 A0 A1 A2 B0 B1 B2 φ p1 p2) ∧
    (A2 ≠ 0 → A1 / A2 ≤ -1 → B1 - B2 * A1 / A2 < 0 →
      ∀ p1 p2 : ℝ, feasible37 A0 A1 A2 φ p1 p2 → p1 ≠ p2 →
        suboptimal37 A0 A1 A2 B0 B1 B2 φ p1 p2) := by sorry

end StaticProphetSec
