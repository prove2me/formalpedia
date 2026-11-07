-- Prove2me | Theorems.Thm_PolygonPack_lemma_A_1
-- name    : PolygonPack.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:27.236303+00:00
-- url     : https://prove2.me/theorems/b943a559-4616-4270-8957-4cf701bc3e49
-- title:
--   Lemma A.1 — direction and band estimates
-- statement:
--   Put $\gamma(D)=\sqrt{D^2-1}$ and $s=1/\sqrt2$.
--
--   1. Let $PQ$ be a segment in the unit square of length $D>1$ following the $u$-diagonal. Then every point of it satisfies $|y-x|\le1-\gamma(D)$, and one endpoint has $u\le-s\gamma(D)$ while the other has $u\ge s\gamma(D)$.
--   2. For $1<D\le\sqrt2$, the band in the square has area
--   $$
--   \bigl|\{(x,y)\in[0,1]^2:\ |y-x|\le1-\gamma(D)\}\bigr|=2-D^2 .
--   $$
--   3. Let two polygons of positive area in one feasible packing have diameter segments of lengths $D_1,D_2>1$ with $\gamma(D_1)+\gamma(D_2)>1$. Then the two placed segments follow the same diagonal.
--
--   The lemma shows how far a long diameter can stray from a diagonal, and it gives the crossing criterion behind all common-diagonal arguments.
--
--   Differences from the source:
--   - encoding: a segment of length D reaching from u ≤ −sγ(D) to u ≥ sγ(D) → one of the two endpoints satisfies each bound, with either order; reason: the printed proof directs the segment, which amounts to the same
--   - reading: diameter segments with lengths D1, D2 in the same feasible packing → two polygons of positive area with D1, D2 > 1; reason: γ is defined for 1 < D on p.21, and the proof on p.21 uses a positive-area polygon
--   - encoding: follow the same diagonal → both or neither of the placed segments has same-sign increments; reason: a segment follows the v-diagonal exactly when it does not follow the u-diagonal (p.21)
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.1, p.21

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_diag
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick

namespace PolygonPack

/-- **Lemma A.1 (Direction and band estimates).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.21. "Put γ(D) = √(D² − 1) for 1 < D ≤ √2. A segment of length D
following the u-diagonal lies in |y − x| ≤ 1 − γ(D) and reaches from u ≤ −sγ(D) to u ≥ sγ(D). The band has area 2 − D² in
the square. Diameter segments with lengths D1, D2 in the same feasible packing must follow the same diagonal if
γ(D1) + γ(D2) > 1."

Three conjuncts:
* a segment `PQ` in the square, of length above one, following the `u`-diagonal: the band and the two reach bounds, with
  either endpoint being the lower one;
* the area of the band, for `1 < D ≤ √2`;
* two polygons of a packing, of positive area, with diameter segments of length above one and `γ(D1) + γ(D2) > 1`.

**Formalization Note.** Two diameters "follow the same diagonal" when both or neither has same-sign increments, since a
segment follows the `v`-diagonal exactly when it does not follow the `u`-diagonal (p.21). The polygons of the third
conjunct have positive area, as the proof on p.21 uses and App. E assumes. -/
theorem lemma_A_1 :
    (∀ P Q : ℝ × ℝ, P ∈ unitSq → Q ∈ unitSq → 1 < eucl P Q → FollowsU P Q →
      (∀ z ∈ segment ℝ P Q, |z.2 - z.1| ≤ 1 - gam (eucl P Q)) ∧
        (((diag P).1 ≤ -(diagS * gam (eucl P Q)) ∧ diagS * gam (eucl P Q) ≤ (diag Q).1) ∨
          ((diag Q).1 ≤ -(diagS * gam (eucl P Q)) ∧ diagS * gam (eucl P Q) ≤ (diag P).1))) ∧
    (∀ D : ℝ, 1 < D → D ≤ Real.sqrt 2 →
      MeasureTheory.volume {z : ℝ × ℝ | z ∈ unitSq ∧ |z.2 - z.1| ≤ 1 - gam D} = ENNReal.ofReal (2 - D ^ 2)) ∧
    (∀ (I : Instance) (S : Finset (Fin I.n)) (T : Fin I.n → Pose), Packs I S T →
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → PosArea (I.verts i) → PosArea (I.verts j) →
      ∀ A B A' B' : ℚ × ℚ, IsDiameterSeg (I.verts i) A B → IsDiameterSeg (I.verts j) A' B' →
        1 < lenD A B → 1 < lenD A' B' → 1 < gam (lenD A B) + gam (lenD A' B') →
        (FollowsU ((T i).act (castPt A)) ((T i).act (castPt B)) ↔
          FollowsU ((T j).act (castPt A')) ((T j).act (castPt B')))) := by sorry

end PolygonPack
