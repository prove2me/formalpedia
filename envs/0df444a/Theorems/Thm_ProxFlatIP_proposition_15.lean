-- Prove2me | Theorems.Thm_ProxFlatIP_proposition_15
-- name    : ProxFlatIP.proposition_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:40.644406+00:00
-- url     : https://prove2.me/theorems/130881e3-173f-4166-a427-901911d56fa4
-- title:
--   Proposition 15 — every $Q$ with $\tau Q=Q^\circ$ and more than six vertices is some $P_v$
-- statement:
--   Let $Q\subseteq\mathbb R^2$ be a polygon with $\tau Q=Q^\circ$ and $|V(Q)|>6$, and let $v\in V(Q)$. Then there exists a polygon $P$ such that $\tau P=P^\circ$, the point $v$ lies in the interior of $\operatorname{stell}(P)\setminus P$, and
--   $$Q=P_v.$$
--
--   This supplies the inductive step: a polygon with many vertices comes from one in a family with fewer vertices at an endpoint.
--
--   Differences from the source: none.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Proposition 15, p.20

import Mathlib
import Definitions.Def_ProxFlatIP_PlanarPolar

open MeasureTheory

namespace ProxFlatIP

/-- **Proposition 15** (arXiv:2211.14941v1, Proposition 15, p.20). If `τQ = Q°` is a polygon with
`|V(Q)| > 6` and `v ∈ V(Q)`, there is a polygon `P` with `τP = P°`, with `v` in the interior of
`stell(P) \ P`, and with `Q = P_v`. -/
theorem proposition_15 (Q : Set Plane) (hQ : IsPolygon Q) (h : tauImage Q = polar Q)
    (hV : 6 < (Set.extremePoints ℝ Q).ncard) (v : Plane) (hv : v ∈ Set.extremePoints ℝ Q) :
    ∃ P : Set Plane, IsPolygon P ∧ tauImage P = polar P ∧ v ∈ interior (stell P \ P) ∧
      Q = modify P v := by sorry

end ProxFlatIP
