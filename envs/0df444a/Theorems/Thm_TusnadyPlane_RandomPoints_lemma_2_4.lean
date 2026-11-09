-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_lemma_2_4
-- name    : TusnadyPlane.RandomPoints.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:28.515787+00:00
-- url     : https://prove2.me/theorems/fad55933-8cdb-477f-9a3c-34af02d8acde
-- title:
--   Lemma 2.4 — Conditional gain
-- statement:
--   For $n\ge1$, $b\ge3$, $h\ge1$, any fixed coloring, and every stage $0\le j<h$, take the actual potential $Z_j$, the information $\mathcal F_j$ of the revealed heights and digits, and the actual comparison-region counts $m_R$. Almost surely under the independent uniform square law,
--   $$\mathbb E[Z_{j+1}-Z_j\mid\mathcal F_j]\ge\delta_j=\frac1{4bM}\sum_R\sqrt{m_R},\qquad M=b^{h-1}.$$
--   The sum includes every comparison rectangle of that transition. The conditional expectation is derived from the point process; it is not a hypothesis about an arbitrary potential. This connects the local comparison to the full scale sequence.
--
--   Differences from the source:
--   - encoding: iid uniform square points and their digit-generated sigma-fields → canonical continuous product Lebesgue law and comap of actual heights and first j digits; reason: equality of the joint law covers every iid realization; digit choices differ only on the countable null boundary set
--   - encoding: one-based labels, ordered cells and real normalizations → Fin-indexed cells, half-open membership and real arithmetic; reason: relabeling preserves all b^h cells and all M comparison rectangles; the null horizontal boundary choices do not change the almost-sure statement
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 9 (PDF p. 10), Lemma 2.4, (11)

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_scales
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Lemma 2.4, printed p.9 / PDF p.10, (11). -/
theorem lemma_2_4 (n b h j : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b)
    (hh : 1 ≤ h) (hj : j < h) (χ : Coloring n) :
    ∀ᵐ P ∂sampleLaw n, delta b h j P ≤
      (condExp (digitSigma n b j) (sampleLaw n)
        (fun Q => potential b h (j+1) χ Q - potential b h j χ Q)) P := by sorry

end TusnadyPlane.RandomPoints
