-- Prove2me | Theorems.Thm_ProxFlatIP_proposition_12
-- name    : ProxFlatIP.proposition_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:32.06395+00:00
-- url     : https://prove2.me/theorems/bfcaab97-7fcb-4d71-bbe9-0d5b91f530c3
-- title:
--   Proposition 12 — the operation $P\mapsto P_v$ preserves $\tau P=P^\circ$
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a polygon with $\tau P=P^\circ$, and let $v\in\operatorname{stell}(P)$. Then
--   $$\tau P_v=(P_v)^\circ.$$
--
--   This is the add-and-cut modification of self-polar polygons, in the plane and for the rotation $\tau$.
--
--   Differences from the source: none.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Proposition 12, p.19 (cf. Jensen, Self-polar polytopes, Theorem 7.4)

import Mathlib
import Definitions.Def_ProxFlatIP_PlanarPolar

open MeasureTheory

namespace ProxFlatIP

/-- **Proposition 12** (arXiv:2211.14941v1, Proposition 12, p.19, cf. Jensen, Theorem 7.4). If
`τP = P°` is a polygon and `v ∈ stell(P)`, then `τP_v = (P_v)°`. -/
theorem proposition_12 (P : Set Plane) (hP : IsPolygon P) (h : tauImage P = polar P)
    (v : Plane) (hv : v ∈ stell P) : tauImage (modify P v) = polar (modify P v) := by sorry

end ProxFlatIP
