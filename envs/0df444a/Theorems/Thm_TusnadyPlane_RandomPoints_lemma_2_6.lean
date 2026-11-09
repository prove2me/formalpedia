-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_lemma_2_6
-- name    : TusnadyPlane.RandomPoints.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:57.522217+00:00
-- url     : https://prove2.me/theorems/c8cd94bf-6989-4c2f-8ccb-f5d177302334
-- title:
--   Lemma 2.6 — Fluctuations
-- statement:
--   Fix $n\ge1$, $b\ge3$, $h\ge1$ and a coloring. Put $M=b^{h-1}$ and form the fluctuation of the actual potential,
--   $$T=\sum_{j<h}(Z_{j+1}-\mathbb E[Z_{j+1}\mid\mathcal F_j]).$$
--   For every $\lambda>0$,
--   $$\Pr(T\le-\lambda)\le\exp\left(-\frac{\lambda^2M^2}{2hn}\right).$$
--   This is the one-sided bound with its exact coefficient and no prefactor. It applies whether or not $M\le n$, and controls fluctuations for each fixed coloring.
--
--   Differences from the source:
--   - encoding: actual iid points, digit information and fluctuation sum (10) → sampleLaw and the explicitly computed potential, digitSigma and fluctuation; reason: joint-law equivalence preserves the probability; the half-open cell and digit boundary conventions differ only on a null set
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 11 (PDF p. 12), Lemma 2.6, (13)

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_scales
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Lemma 2.6, printed p.11 / PDF p.12, (13). -/
theorem lemma_2_6 (n b h : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b) (hh : 1 ≤ h)
    (χ : Coloring n) (lam : ℝ) (hlam : 0 < lam) :
    (sampleLaw n).real {P | fluctuation b h χ P ≤ -lam} ≤
      Real.exp (-(lam^2 * (comparisonCount b h : ℝ)^2 / (2*(h : ℝ)*n))) := by sorry

end TusnadyPlane.RandomPoints
