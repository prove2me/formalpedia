-- Prove2me | Theorems.Thm_PolygonPack_lemma_A_4
-- name    : PolygonPack.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:15.473648+00:00
-- url     : https://prove2.me/theorems/99a76e62-dcc7-404f-9e99-33d9171c4e5c
-- title:
--   Lemma A.4 — a witness for each small latest start
-- statement:
--   Let $c>0$ and $h_0\le\min\{c/16,\,1/16,\,1/(8K)\}$. Let $P$ be a polygon of positive area with a diameter segment of length $D>1$, thickness $h$, placed in the square so that the diameter follows the chosen diagonal.
--
--   1. If $c\delta<h\le h_0$ and the canonical bottom satisfies $d\le t$ with $t\ge0$, then $P$ meets $[-Kh,Kh]\times[-t,t]$.
--   2. If $h\le c\delta$, the diameter meets $u=0$ at a point with
--   $$
--   |v|\le B(D)=\frac{1-\gamma}{\sqrt2(1+\gamma)} ,
--   $$
--   and if moreover $c<1/2$, $\delta/2-h\le t$, $t\ge0$ and $\delta\le1/16$, this point satisfies $|v|\le t/[(1-2c)(1-\delta)^2]$.
--
--   Polygons with a small latest start thus cannot avoid a small region around the centre of the square.
--
--   Differences from the source:
--   - generalization: a Tight polygon, a Slack polygon → h > cδ with h ≤ h0, and h ≤ cδ, with no area condition; reason: membership in the classes implies these when h0 = 2a0
--   - generalization: the fixed diameter segment of P → every diameter segment AB; reason: the fixed one is one of them
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - reading: the last bound of the Slack clause, with no range for c printed in the lemma → c < 1/2 for that bound; reason: 0 < c < 1/2 is the paper's range for c on p.5 and it makes the denominator positive
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.4, p.26 (eq. (9))

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_diag
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_polyArea
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_IsTight
import Definitions.Def_PolygonPack_Kc

namespace PolygonPack

/-- **Lemma A.4 (A witness for each small latest start).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.26. "Take h0 ≤ min{c/16, 1/16, 1/(8K)}. In a chosen-diagonal
placement, a Tight polygon with canonical bottom d ≤ t, t ≥ 0, meets W_P := [−Kh, Kh] × [−t, t]. For a Slack polygon following the
same diagonal, put d = δ/2 − h. Its diameter meets u = 0 at a point with |v| ≤ B(D) := (1 − γ)/(√2(1 + γ)). (9) If d ≤ t and δ ≤ 1/16,
this point satisfies |v| ≤ t/[(1 − 2c)(1 − δ)²]."

**Formalization Note.** Classes are used through `h > cδ`, `h ≤ h0` for Tight and `h ≤ cδ` for Slack, for every diameter segment. A
negative `d` is allowed for a Tight polygon. The last bound carries `c < 1/2` (the paper's standing range for `c`, p.5), which makes its
denominator positive. -/
theorem lemma_A_4 (c h0 : ℝ) (hc : 0 < c) (hh0 : h0 ≤ c / 16 ∧ h0 ≤ 1 / 16 ∧ h0 ≤ 1 / (8 * Kc c)) (v : List (ℚ × ℚ))
    (A B : ℚ × ℚ) (hpos : PosArea v) (hd : IsDiameterSeg v A B) (hD : 1 < lenD A B) (T : Pose) (hT : IsPlacement v T)
    (hC : ChosenDiag A B T) :
    (c * deficit (lenD A B) < thick v A B → thick v A B ≤ h0 → ∀ t : ℝ, 0 ≤ t → canonBottom v A B ≤ t →
      ∃ q ∈ placedUV v T, |q.1| ≤ Kc c * thick v A B ∧ |q.2| ≤ t) ∧
    (thick v A B ≤ c * deficit (lenD A B) →
      ∃ q ∈ diag '' segment ℝ (T.act (castPt A)) (T.act (castPt B)), q.1 = 0 ∧ |q.2| ≤ bD (gam (lenD A B)) ∧
        ∀ t : ℝ, 0 ≤ t → c < 1 / 2 → deficit (lenD A B) / 2 - thick v A B ≤ t → deficit (lenD A B) ≤ 1 / 16 →
          |q.2| ≤ t / ((1 - 2 * c) * (1 - deficit (lenD A B)) ^ 2)) := by sorry

end PolygonPack
