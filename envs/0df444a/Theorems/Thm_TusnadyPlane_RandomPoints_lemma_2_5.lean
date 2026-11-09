-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_lemma_2_5
-- name    : TusnadyPlane.RandomPoints.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:44.470556+00:00
-- url     : https://prove2.me/theorems/7a8bd753-8f42-4fdc-85ff-95228a63ba44
-- title:
--   Lemma 2.5 — Good transitions
-- statement:
--   Let $n\ge1$, $b\ge3$, $h\ge1$, $M=b^{h-1}$, and $0\le j<h$. A transition is good when at least $n/2$ points lie in inner regions whose counts satisfy $m_R\le bn/M$. Write $G_j$ for this event and $G=\bigcap_{j<h}G_j$. With $\delta_j$ and $\delta_*$ computed from the sample,
--   $$G_j\implies\delta_j\ge\delta_*=\frac1{8b^{3/2}}\sqrt{n/M}\quad\text{almost surely}.$$
--   If $M\le n$, both probability bounds hold:
--   $$\Pr(G_j^c)\le(48/b)^{n/2},\qquad\Pr(G^c)\le h(48/b)^{n/2}.$$
--   The first clause has no $M\le n$ requirement. These events are common to all colorings and control the available gains at each scale.
--
--   Differences from the source:
--   - encoding: on G_j under the section probability-one convention, followed by both probability bounds → an almost-sure implication conjoined with an implication from M≤n to both real probability bounds under sampleLaw; reason: this keeps the source domain, the separate condition for part (ii), and both clauses; boundary points are not conditioned away
--   - encoding: strict heaviness m_R>bn/M and threshold n/2 → non-heavy counts use ≤ and goodness uses ≥ with real division and real exponent n/2; reason: these are the exact complementary comparisons, including odd n
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 10 (PDF p. 11), Lemma 2.5, (i)–(ii), (12)

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_scales
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Lemma 2.5, printed p.10 / PDF p.11, both clauses. -/
theorem lemma_2_5 (n b h j : ℕ) (hn : 1 ≤ n) (hb : 3 ≤ b)
    (hh : 1 ≤ h) (hj : j < h) :
    (∀ᵐ P ∂sampleLaw n, P ∈ GoodTransition n b h j → deltaStar n b h ≤ delta b h j P) ∧
    (comparisonCount b h ≤ n →
      (sampleLaw n).real (GoodTransition n b h j)ᶜ ≤ (48/(b : ℝ))^((n : ℝ)/2) ∧
      (sampleLaw n).real (AllGood n b h)ᶜ ≤ (h : ℝ)*(48/(b : ℝ))^((n : ℝ)/2)) := by sorry

end TusnadyPlane.RandomPoints
