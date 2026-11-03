-- Prove2me | Theorems.Thm_ProxFlatIP_proposition_5
-- name    : ProxFlatIP.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:26.495883+00:00
-- url     : https://prove2.me/theorems/7ddb37a5-8fc8-4f8e-8646-14e70ce9f46a
-- title:
--   Proposition 5 — $\tau P=P^\circ$ forces at least six vertices
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a polygon with $\tau P=P^\circ$. Then
--   $$|V(P)|\ge6.$$
--
--   Together with Proposition 7, this is the base of the induction on the number of vertices that proves Lemma 4.
--
--   Differences from the source: none.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Proposition 5, p.16

import Mathlib
import Definitions.Def_ProxFlatIP_PlanarPolar

open MeasureTheory

namespace ProxFlatIP

/-- **Proposition 5** (arXiv:2211.14941v1, Proposition 5, p.16). If `τP = P°` is a polygon, then
`|V(P)| ≥ 6`. -/
theorem proposition_5 (P : Set Plane) (hP : IsPolygon P) (h : tauImage P = polar P) :
    6 ≤ (Set.extremePoints ℝ P).ncard := by sorry

end ProxFlatIP
