-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_theorem_1_1
-- name    : TusnadyPlane.RandomPoints.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:57.303368+00:00
-- url     : https://prove2.me/theorems/1a703d90-ea23-49f5-99e2-bdb4f3de3e7b
-- title:
--   Theorem 1.1 — Random points force large discrepancy for every coloring
-- statement:
--   For every real $A>0$, there exists a constant $c_A>0$, depending only on $A$, such that for every integer $n\ge1$, $n$ independent uniform points $P_i=(U_i,V_i)$ in $[0,1]^2$ satisfy
--   $$\Pr\left[\forall\chi\in\{\pm1\}^n:\|F_\chi\|_\infty\ge c_A(\log_2 n)^{3/2}\right]\ge1-\exp(-An).$$
--   Here $F_\chi(x,y)$ is the signed count in the closed anchored rectangle $[0,x]\times[0,y]$ and its norm is the supremum over the full square. Every coloring is inside the probability event, including sample-dependent choices. No distinctness or good-sample condition is a hypothesis. This is the paper's random-point lower bound at the full exponential failure rate, including $n=1$.
--
--   Differences from the source:
--   - encoding: any n independent uniform points in the unit square → the n-fold product of the area-one restricted Lebesgue square law; reason: the conclusion concerns only the joint sample, so equality of law covers every iid realization without a good-sample restriction
--   - encoding: labeled points, signs ±1 and log₂ → Fin n labels, Boolean signs and Real.log n / Real.log 2 with real exponent 3/2; reason: these are exact relabeling and notation conventions; n≥1 includes n=1 and c_A is quantified before n
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 1 (PDF p. 2), Theorem 1.1

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_sample
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Theorem 1.1, printed p.1 / PDF p.2. The constant precedes n. -/
theorem theorem_1_1 (A : ℝ) (hA : 0 < A) :
    ∃ cA : ℝ, 0 < cA ∧ ∀ n : ℕ, 1 ≤ n →
      1 - Real.exp (-A*(n : ℝ)) ≤
        (sampleLaw n).real {P | ∀ χ : Coloring n,
          cA * (Real.log (n : ℝ)/Real.log 2)^(3/2 : ℝ) ≤ discrepancy P χ} := by sorry

end TusnadyPlane.RandomPoints
