-- Prove2me | Theorems.Thm_PolygonPack_lemma_A_5
-- name    : PolygonPack.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:57.547568+00:00
-- url     : https://prove2.me/theorems/af696159-a23c-455e-bddf-fd6ccb19ca5f
-- title:
--   Lemma A.5 — length after removing the two extreme sections
-- statement:
--   Let $0<c\le1/400$, $a_0>0$, and let $h_0=2a_0$ satisfy $h_0\le\min\{c/400,\,1/(500K),\,1/(300LK),\,1/16\}$. Let $F$ be a family of polygons of a valid instance.
--
--   1. If $t_0\le1/1000$, $0\le t\le t_0$, and every polygon of $F$ is Tight with $d\le t$ or Slack with $\delta/2-h\le t$, then in every packing of $F$ the fixed diameters follow one diagonal, and a packing exists in which it is the $u$-diagonal. In every packing of that kind the bottommost and topmost central sections exist when $F\ne\emptyset$, and after their removal the remaining sections have total length
--   $$
--   W\le\frac{2B^*+10Kh_0}{1-6LKh_0}\,t,\qquad B^*=\frac1{(1-2c)\bigl(1-2t_0/(1-2c)\bigr)^2}.
--   $$
--   2. If every polygon of $F$ is Tight with $d\le t$ for some $t\ge0$, the same holds with $W\le 2t/(1-6LKh_0)$.
--   3. For every $c,\eta>0$ there is $\bar h>0$ such that, for every $a_0>0$ with $2a_0\le\bar h$, every family as in 2 has $W\le(2+\eta)t$.
--
--   If $|F|\le2$ the sum is empty and $W=0$. The lemma is what bounds the total load of polygons with small latest starts, and it drives the seven-track schedule.
--
--   Differences from the source:
--   - reading: Tight-only bound in the lemma, and fixed c ≤ 1/400, t0 ≤ 1/1000 → the Tight-only bound for every t ≥ 0, with no t0; reason: p.28: it applies for every t ≥ 0, independently of t0
--   - generalization: the last sentence, with c ≤ 1/400 fixed → every c > 0; reason: p.28 proves it for any fixed c > 0
--   - encoding: rotate the packing by a quarter-turn if necessary → a normalized packing exists, and the bounds hold for every normalized packing and every pair of extreme polygons; reason: a quarter-turn about the centre carries a packing to a packing
--   - encoding: remove the bottommost and topmost sections, or all polygons if at most two → the sum over F \ {b, t} for extreme b, t, whose existence is a conjunct; reason: this sum is empty when |F| ≤ 2
--   - generalization: the retained-section assertion of Lemma 2.2 for prescribed η, on Tight polygons with 0 < d ≤ t, t > 0 → W ≤ (2 + η)t for Tight polygons with d ≤ t, t ≥ 0, for every cutoff below a threshold; reason: p.28 proves the Tight-only bound for every t ≥ 0 and any sign of d; the family of Lemma 2.2 is a special case
--   - reading: a cutoff h0 → h0 = 2·a0 with a0 > 0 in the classes; reason: p.20: every Slack or Tight polygon has h < h0 := 2a0
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma A.5, p.27 (eq. (10)); proof, p.28

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
import Definitions.Def_PolygonPack_IsCentralBottom

namespace PolygonPack

/-- **Lemma A.5 (Length after removing the two extreme sections).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.27. "Fix c ≤ 1/400 and t0 ≤ 1/1000. Consider a feasible packing of
Tight and Slack polygons, where each Slack polygon is assigned the diagonal latest start d = δ/2 − h. Suppose every polygon satisfies
d ≤ t ≤ t0 for some t ≥ 0; negative canonical bottoms are permitted for Tight polygons. Assume h0 ≤ min{c/400, 1/(500K), 1/(300LK), 1/16}.
Rotate the packing by a quarter-turn if necessary so that its common diagonal (established below) is the u-diagonal. Remove the bottommost and
topmost sections on u = 0, or remove all polygons if there are at most two. The remaining sections have total length W satisfying
W ≤ ((2B∗ + 10Kh0)/(1 − 6LKh0)) t, B∗ = 1/((1 − 2c)(1 − 2t0/(1 − 2c))²). (10) For a family of Tight polygons alone, the sharper bound is
W ≤ 2t/(1 − 6LKh0). Thus, for every prescribed η > 0, the retained-section assertion of Lemma 2.2 follows by taking h0 sufficiently small for
fixed c."

With `h0 = 2·a0` (p.20) the statement has the mixed bound (10); the Tight-only bound for every `t ≥ 0`, which is "independently of t0" (p.28); and the
last sentence, for every `c > 0` as on p.28 ("For any fixed c > 0"). In the first two, the diameters share a diagonal and a normalized packing exists.

**Formalization Note.** `Packs` is closed under the quarter-turn about the centre of the square, so "rotate if necessary" is the existence of a
normalized `T'`, and the bounds are stated for every normalized packing `T` and every pair of extreme polygons. The extreme polygons exist whenever
`F` is nonempty; `F \ {b, t}` is empty when `|F| ≤ 2`, so `W = 0` there. -/
theorem lemma_A_5 :
    (∀ c a0 : ℝ, 0 < c → c ≤ 1 / 400 → 0 < a0 → IsA5Cutoff c (2 * a0) →
      ∀ (I : Instance), I.Valid → ∀ F : Finset (Fin I.n),
      (∀ t0 t : ℝ, t0 ≤ 1 / 1000 → 0 ≤ t → t ≤ t0 → (∀ i ∈ F, JobBelow c a0 (I.verts i) t) →
        (∀ T, Packs I F T → SameDiagonal I T F ∧ ∃ T', Packs I F T' ∧ IsNormalized I T' F) ∧
        ∀ T, Packs I F T → IsNormalized I T F →
          (F.Nonempty → ∃ b t', IsCentralBottom I T F b ∧ IsCentralTop I T F t') ∧
          ∀ b t', IsCentralBottom I T F b → IsCentralTop I T F t' →
            retainedW I T F b t' ≤
              (2 * bStar c t0 + 10 * Kc c * (2 * a0)) / (1 - 6 * Lc c * Kc c * (2 * a0)) * t) ∧
      (∀ t : ℝ, 0 ≤ t → (∀ i ∈ F, IsTight c a0 (I.verts i) ∧ canonD (I.verts i) ≤ t) →
        (∀ T, Packs I F T → SameDiagonal I T F ∧ ∃ T', Packs I F T' ∧ IsNormalized I T' F) ∧
        ∀ T, Packs I F T → IsNormalized I T F →
          (F.Nonempty → ∃ b t', IsCentralBottom I T F b ∧ IsCentralTop I T F t') ∧
          ∀ b t', IsCentralBottom I T F b → IsCentralTop I T F t' →
            retainedW I T F b t' ≤ 2 * t / (1 - 6 * Lc c * Kc c * (2 * a0)))) ∧
    (∀ c η : ℝ, 0 < c → 0 < η → ∃ hbar : ℝ, 0 < hbar ∧ ∀ a0 : ℝ, 0 < a0 → 2 * a0 ≤ hbar →
      ∀ (I : Instance), I.Valid → ∀ (F : Finset (Fin I.n)) (t : ℝ), 0 ≤ t →
        (∀ i ∈ F, IsTight c a0 (I.verts i) ∧ canonD (I.verts i) ≤ t) →
        ∀ T, Packs I F T → IsNormalized I T F → ∀ b t', IsCentralBottom I T F b → IsCentralTop I T F t' →
          retainedW I T F b t' ≤ (2 + η) * t) := by sorry

end PolygonPack
