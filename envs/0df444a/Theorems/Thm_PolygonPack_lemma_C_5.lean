-- Prove2me | Theorems.Thm_PolygonPack_lemma_C_5
-- name    : PolygonPack.lemma_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:30.027359+00:00
-- url     : https://prove2.me/theorems/77da7022-13e6-4a88-b8c4-9cc8953e932d
-- title:
--   Lemma C.5 — the adaptive prefix coefficient
-- statement:
--   Let $0<c\le1/24$ and $a_0>0$. Let $F$ be a feasible family of Slack polygons of a valid instance, with largest diameter $M>D_0=2/\sqrt3$. Let $a=\cos\phi$, $b=\sin\phi$ be the repaired angle for $M$, and $C(D)=a+b-2abD$.
--
--   1. If $1<D\le M$ and $h\le c(\sqrt2-D)$, then $Da+hb\le1$ and $Db+ha\le1$.
--   2. For $1\le D\le M$,
--   $$
--   \sum_{i\in F,\ D_i\ge D}h_i\le\alpha_{\mathrm{ad}}\,C(D),\qquad\alpha_{\mathrm{ad}}=\frac{R+4\sqrt2c}{1-12c},\quad R=2+2\sqrt2 .
--   $$
--   This is the source of the factor $R=2+2\sqrt2$ in the approximation ratio.
--
--   Differences from the source:
--   - generalization: every Slack enclosure with 1 < D ≤ M fits → for all real D, h with 1 < D ≤ M and h ≤ c(√2 − D), both span inequalities; reason: Lemma C.2 states it in this form; every Slack enclosure is such a pair
--   - reading: the largest comparison Slack diameter M > D0, the repaired angle → a feasible family of Slack polygons with a member of largest D, and the hypothesis 0 < c ≤ 1/24 of Lemma C.2; reason: that lemma defines the repaired angle
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma C.5, p.35; Lemma C.2, p.32; H(D), p.33

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
import Definitions.Def_PolygonPack_clearance
open Classical

namespace PolygonPack

/-- **Lemma C.5 (The adaptive prefix coefficient).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.35. "At the repaired angle for the largest comparison Slack diameter M > D0, every Slack enclosure with
1 < D ≤ M fits, and H(D) ≤ α_ad C(D) (1 ≤ D ≤ M), α_ad = (R + 4√2c)/(1 − 12c)."

`H(D)` is the total thickness of comparison Slack polygons with diameter at least `D` (p.33). The comparison family `F` is feasible and all Slack, polygon `m` has its
largest diameter `M`, and `0 < c ≤ 1/24` is the hypothesis of Lemma C.2, whose repaired angle this is.

**Formalization Note.** "Fits" is both span inequalities of Lemma C.1, `Da + hb ≤ 1` and `Db + ha ≤ 1`, stated as in Lemma C.2 for every `D`, `h` with `1 < D ≤ M` and
`h ≤ c(√2 − D)`. `M < √2` follows from positive area (p.36), so it is not a hypothesis. -/
theorem lemma_C_5 (c a0 : ℝ) (hc : 0 < c) (hc' : c ≤ 1 / 24) (ha0 : 0 < a0) (I : Instance) (hI : I.Valid) (F : Finset (Fin I.n))
    (hF : Feasible I F) (hSlack : ∀ i ∈ F, IsSlack c a0 (I.verts i)) (m : Fin I.n) (hm : m ∈ F)
    (hmax : ∀ i ∈ F, polyD (I.verts i) ≤ polyD (I.verts m)) (hM : constD0 < polyD (I.verts m)) :
    (∀ D h : ℝ, 1 < D → D ≤ polyD (I.verts m) → h ≤ c * (Real.sqrt 2 - D) →
      D * repairCos c (polyD (I.verts m)) + h * repairSin c (polyD (I.verts m)) ≤ 1 ∧
      D * repairSin c (polyD (I.verts m)) + h * repairCos c (polyD (I.verts m)) ≤ 1) ∧
    ∀ D : ℝ, 1 ≤ D → D ≤ polyD (I.verts m) →
      ∑ i ∈ F.filter (fun i => D ≤ polyD (I.verts i)), polyH (I.verts i) ≤
        alphaAd c * clr (repairCos c (polyD (I.verts m))) (repairSin c (polyD (I.verts m))) D := by sorry

end PolygonPack
