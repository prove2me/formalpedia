-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_4
-- name    : ProxFlatIP.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:32.487504+00:00
-- url     : https://prove2.me/theorems/c4c1781c-00ae-40b9-97cc-eb92356100a9
-- title:
--   Lemma 4 — $\tau Q\subseteq Q^\circ$ implies $\mathrm{vol}_2(Q^\circ)\ge3$
-- statement:
--   Let $Q\subseteq\mathbb R^2$ be a polygon with $\tau Q\subseteq Q^\circ$, where $\tau$ is the $90^\circ$ counterclockwise rotation. Then
--   $$\mathrm{vol}_2(Q^\circ)\ge3.$$
--
--   This is the planar extremal fact behind the constant of the paper: it gives $\kappa_3<4/3$, and through it the coefficient $4/9$ of $n$ in the proximity bound. The constant is attained by hexagons with $\tau P=P^\circ$ (Proposition 7).
--
--   Differences from the source:
--   - generalization: polygon → the convex hull of any finite set, including degenerate hulls; reason: in the degenerate cases Q° is unbounded with nonempty interior, so the inequality holds with area ∞; the full-dimensional case is the printed one
--   - encoding: vol₂(Q°) ≥ 3 → 3 ≤ volume in ℝ≥0∞; reason: Q° may be unbounded, and then its area is ∞
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 4, p.8; proved in Appendix A, p.23

import Mathlib
import Definitions.Def_ProxFlatIP_PlanarPolar

open MeasureTheory

namespace ProxFlatIP

/-- **Lemma 4** (arXiv:2211.14941v1, Lemma 4, p.8; proof in Appendix A, p.23). If `Q` is a polygon
with `τQ ⊆ Q°`, then `vol₂(Q°) ≥ 3`.

**Formalization Note.** The area is in `ℝ≥0∞`. `IsPolygon` includes degenerate hulls and hulls with
`0` outside the interior; for those `Q°` is unbounded with nonempty interior and has infinite area. -/
theorem lemma_4 (Q : Set Plane) (hQ : IsPolygon Q) (h : tauImage Q ⊆ polar Q) :
    3 ≤ volume (polar Q) := by sorry

end ProxFlatIP
