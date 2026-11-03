-- Prove2me | Theorems.Thm_ProxFlatIP_proposition_9
-- name    : ProxFlatIP.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:13.684301+00:00
-- url     : https://prove2.me/theorems/c9a11a69-f7fa-4a23-9263-165d22f7af29
-- title:
--   Proposition 9 — a symmetric polygon with $\tau P\subseteq P^\circ$ sits below some $\tau Q=Q^\circ$
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a symmetric polygon with $\tau P\subseteq P^\circ$. Then there exists a polygon $Q$ such that
--   $$\tau P\subseteq\tau Q=Q^\circ\subseteq P^\circ.$$
--
--   This reduces the area bound of Lemma 4 to the extremal polygons, those with $\tau Q=Q^\circ$.
--
--   Differences from the source:
--   - generalization: polygon (full-dimensional, for P° to be a polygon) → the convex hull of any finite set, including degenerate hulls; reason: for a segment [−p,p] or {0} or ∅ the statement still holds, using an SL₂ image of a hexagon with τQ = Q° containing p; the full-dimensional case is the printed one
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Proposition 9, p.17 (cf. Jensen, Self-polar polytopes, Corollary 7.3)

import Mathlib
import Definitions.Def_ProxFlatIP_PlanarPolar

open MeasureTheory

namespace ProxFlatIP

/-- **Proposition 9** (arXiv:2211.14941v1, Proposition 9, p.17, cf. Jensen, Corollary 7.3). If `P` is
a symmetric polygon with `τP ⊆ P°`, there is a polygon `Q` with `τP ⊆ τQ = Q° ⊆ P°`.

**Formalization Note.** `IsPolygon` includes degenerate hulls, so this is also stated for those; for
them the statement still holds. -/
theorem proposition_9 (P : Set Plane) (hP : IsPolygon P) (hsym : IsSymmetric P)
    (h : tauImage P ⊆ polar P) :
    ∃ Q : Set Plane, IsPolygon Q ∧ tauImage P ⊆ tauImage Q ∧ tauImage Q = polar Q ∧
      polar Q ⊆ polar P := by sorry

end ProxFlatIP
