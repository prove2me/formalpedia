-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_proposition_2_7
-- name    : TusnadyPlane.RandomPoints.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:49.203554+00:00
-- url     : https://prove2.me/theorems/b91268c9-f39e-47c3-989d-cf2262215ae3
-- title:
--   Proposition 2.7 — Simultaneous probability bound
-- statement:
--   Let $n\ge1$, $b\ge3$, $h\ge1$ be integers, and put $M=b^{h-1}\le n$. For $n$ independent uniform points in the square, the probability that some coloring has small anchored discrepancy satisfies
--   $$\Pr\left[\exists\chi\in\{\pm1\}^n:\|F_\chi\|_\infty\le\frac{h}{64b^{3/2}}\sqrt{n/M}\right]\le h(48/b)^{n/2}+2^n\exp\left(-\frac{hM}{2048b^3}\right).$$
--   The coloring may be selected after observing the sample: its existence belongs inside the event. The non-strict threshold and both summands are retained for all admissible parameters, before the later parameter choice. This is the simultaneous finite-parameter input for the goal.
--
--   Differences from the source:
--   - encoding: independent continuous uniform points and ±1 colorings → canonical product square law and every Bool-valued coloring of Fin n; reason: every iid joint law is the canonical law and Boolean signs biject with ±1; the event retains the full continuum supremum
--   - encoding: fractional powers and n/2 → real powers and real division; reason: constants 64, 48 and 2048 and the exponent b^3 are unchanged
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 11 (PDF p. 12), Proposition 2.7, (14)

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_scales
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Proposition 2.7, printed p.11 / PDF p.12, (14). -/
theorem proposition_2_7 (n b h : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b) (hh : 1 ≤ h)
    (hM : comparisonCount b h ≤ n) :
    (sampleLaw n).real {P | ∃ χ : Coloring n, discrepancy P χ ≤
      (h : ℝ)/(64*(b : ℝ)^(3/2 : ℝ)) * Real.sqrt ((n : ℝ)/comparisonCount b h)} ≤
      (h : ℝ)*(48/(b : ℝ))^((n : ℝ)/2) +
        (2 : ℝ)^n * Real.exp (-((h : ℝ)*comparisonCount b h/(2048*(b : ℝ)^3))) := by sorry

end TusnadyPlane.RandomPoints
