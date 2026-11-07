-- Prove2me | Theorems.Thm_PolygonPack_lemma_C_6
-- name    : PolygonPack.lemma_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:15.434593+00:00
-- url     : https://prove2.me/theorems/76997c5a-5bcb-47fc-a795-2a85af6476c0
-- title:
--   Lemma C.6 — diagonal prefixes with a Tight anchor
-- statement:
--   Let $c,a_0>0$, $1<D_B<\sqrt2$, and suppose $\sqrt2-2a_0/c>1$ and
--   $$
--   \sqrt{(\sqrt2-2a_0/c)^2-1}+\sqrt{D_B^2-1}>1 .
--   $$
--   Let $F$ be a feasible family of a valid instance that contains a Tight polygon. Then, for every $q>0$,
--   $$
--   \sum_{i\in F\text{ Slack},\ \sqrt2-D_i\le q}h_i\le\alpha_{\mathrm{an}}q,\qquad\alpha_{\mathrm{an}}=\max\Bigl\{2+\frac{2\sqrt2+4\sqrt2c}{D_B},\ \frac2{D_B(\sqrt2-D_B)}\Bigr\}.
--   $$
--   The Tight polygon may belong to $T^0$. This bound makes Slack polygons schedulable on the diagonal when a Tight polygon is present.
--
--   Differences from the source:
--   - encoding: a comparison packing containing any Tight polygon, with its Slack polygons → a feasible family F with a Tight member; the sum runs over its Slack members with q_i ≤ q; reason: the same family, written with a filter
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma C.6, p.36

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

/-- **Lemma C.6 (Diagonal prefixes with a Tight anchor).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.36. "Fix 1 < D_B < √2 and put h0 = 2a0. Suppose √2 − h0/c > 1 and
√((√2 − h0/c)² − 1) + √(D_B² − 1) > 1. In a comparison packing containing any Tight polygon, put q_i = √2 − D_i for each Slack polygon. Then, for every q > 0,
Σ_{q_i≤q} h_i ≤ α_an q, α_an = max{2 + (2√2 + 4√2c)/D_B, 2/(D_B(√2 − D_B))}. The Tight polygon may belong to T0."

**Formalization Note.** The first term of `α_an` is `2 + (2√2 + 4√2c)/D_B`, read from the rendered p.36. The sum runs over the Slack polygons of `F` with `q_i ≤ q`, and `F`
may hold other polygons. -/
theorem lemma_C_6 (c a0 DB : ℝ) (hc : 0 < c) (ha0 : 0 < a0) (hDB : 1 < DB) (hDB' : DB < Real.sqrt 2)
    (h1 : 1 < Real.sqrt 2 - 2 * a0 / c) (h2 : 1 < gam (Real.sqrt 2 - 2 * a0 / c) + gam DB) (I : Instance) (hI : I.Valid)
    (F : Finset (Fin I.n)) (hF : Feasible I F) (m : Fin I.n) (hm : m ∈ F) (hTight : IsTight c a0 (I.verts m)) (q : ℝ) (hq : 0 < q) :
    ∑ i ∈ F.filter (fun i => IsSlack c a0 (I.verts i) ∧ Real.sqrt 2 - polyD (I.verts i) ≤ q), polyH (I.verts i) ≤
      alphaAn c DB * q := by sorry

end PolygonPack
