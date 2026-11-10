-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_36
-- name    : StackingStars.Main.lemma_36
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:46:02.753509+00:00
-- url     : https://prove2.me/theorems/74e347c6-c93c-4a5c-aae2-48a590c3832b
-- title:
--   Lemma 36 — polynomial-time rotations and packing into convex mini-containers of total area O(log n) · OPT_rot
-- statement:
--   There are an admissible deterministic real-RAM program $A$, an exponent $k$ and a universal constant $K$ with the following property. On the encoding of every list of $n\ge1$ stars $P$, $A$ halts within $N^k+k$ steps. It outputs for each star a pose $(a,b,x,y)$ with $a^2+b^2=1$ (a proper rotation followed by a translation) and a mini-container label. The mini-container $B$ of a label is the convex hull of the placed stars carrying that label. The output satisfies:
--
--   * placed stars with a common label have pairwise disjoint interiors;
--   * $\sum_B|B|\le K(1+\log n)\,\mathrm{OPT}_{\mathrm{rot}}(P)$;
--   * every mini-container $B$ satisfies $\operatorname{span}_z(B)\le K\,\operatorname{span}_z(P)$ for every unit direction $z$ and every star $P$ that $B$ contains, where $P$ is taken in its rotated position.
--
--   Differences from the source:
--   - reading: in polynomial time, we can compute a rotation of each star and a packing → an admissible program of the published real RAM halting within N^k + k steps that outputs a rigid pose per star; reason: the paper names no model and its coordinates are real; a pose is a rotation followed by a translation
--   - reading: O(log n) and O(span_z(P)) → K · (1 + log n) and K · span_z(P) with one universal K; reason: log 1 = 0 at n = 1; asymptotic notation made explicit
--   - encoding: a packing into a set of convex mini-containers → per star a pose and a label; the mini-container of a label is the convex hull of its placed stars; reason: any convex mini-container contains that hull and the hull is one, so both clauses hold for some containers exactly when they hold for the hulls
--   - encoding: every direction z → every unit vector z; reason: span_z scales with |z|
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 29, Lemma 36

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_Machine

namespace StackingStars.Main

open MatMulTimeLP

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 29 (PDF 31), Lemma 36. One admissible deterministic real-RAM program `A`, one exponent `k` and
one universal `K`: on the encoding of every list of `n ≥ 1` stars, `A` halts within `N^k + k`
steps and writes, for each star `i`, a pose `(out (5i), …, out (5i+3))` (a proper rotation and a
translation, `a² + b² = 1`) and a mini-container label `out (5i+4)`. The mini-container of a label
is the convex hull of its placed stars. Placed stars with a common label have pairwise disjoint
interiors; the total area of the mini-containers is at most `K (1 + log n) OPT_rot(P)`; and every
mini-container `B` satisfies `span_z(B) ≤ K span_z(P)` for every unit direction `z` and every star
`P` it contains, `P` in its rotated position. -/
theorem lemma_36 :
    ∃ (A : Program) (k : ℕ) (K : ℝ), FewInnerTSP.Admissible A ∧ 0 < K ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      RunsWithin A (polysInput P) (polyBound k (totalVerts P)) fun out =>
        (∀ i : Fin n, (blockPose 5 out i).IsRigid) ∧
        (∀ i i' : Fin n, i ≠ i' → out (5 * i + 4) = out (5 * i' + 4) →
          Disjoint (interior ((blockPose 5 out i).act '' region (P i)))
            (interior ((blockPose 5 out i').act '' region (P i')))) ∧
        (∑ ℓ ∈ Finset.univ.image (fun i : Fin n => out (5 * i + 4)),
            hullArea (⋃ j ∈ {j : Fin n | out (5 * j + 4) = ℓ},
              (blockPose 5 out j).act '' region (P j)) ≤
          K * (1 + Real.log n) * optRot (fun i => region (P i))) ∧
        ∀ (i : Fin n) (z : Pt), len z = 1 →
          spanIn z (convexHull ℝ (⋃ j ∈ {j : Fin n | out (5 * j + 4) = out (5 * i + 4)},
              (blockPose 5 out j).act '' region (P j))) ≤
            K * spanIn z ((blockPose 5 out i).act '' region (P i)) := by sorry

end StackingStars.Main
