-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_26
-- name    : StackingStars.Main.lemma_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:28.772199+00:00
-- url     : https://prove2.me/theorems/dbc17248-a0f4-4a0e-af2d-cd6b300b9713
-- title:
--   Lemma 26 — polynomial-time translational packing into convex mini-containers of total area O(log n) · OPT with the span condition (16)
-- statement:
--   There are an admissible deterministic real-RAM program $A$, an exponent $k$ and a universal constant $K$ with the following property. On the encoding of every list of $n\ge1$ stars $P$, $A$ halts within $N^k+k$ steps, where $N$ is the total number of vertices. It outputs for each star a translation and a mini-container label. The mini-container $B$ of a label is the convex hull of the translated stars carrying that label. The output satisfies:
--
--   * stars with a common label have pairwise disjoint interiors;
--   * $\sum_B|B|\le K(1+\log n)\,\mathrm{OPT}_{\mathrm{trans}}(P)$;
--   * every mini-container $B$ satisfies
--   $$\operatorname{span}_z(B)\ \le\ K\,\operatorname{span}_z(P)\qquad(16)$$
--   for every unit direction $z$ and every star $P$ that $B$ contains.
--
--   Differences from the source:
--   - reading: in polynomial time, we can compute → an admissible program of the published real RAM halting within N^k + k steps, k fixed before the input; reason: the paper names no model and its coordinates are real
--   - reading: O(log n) and O(span_z(P)) → K · (1 + log n) and K · span_z(P) with one universal K; reason: log 1 = 0 at n = 1; asymptotic notation made explicit
--   - encoding: a packing into a set of convex mini-containers → per star a translation and a label; the mini-container of a label is the convex hull of its stars; reason: any convex mini-container contains that hull and the hull is one, so both clauses hold for some containers exactly when they hold for the hulls
--   - encoding: every direction z → every unit vector z; reason: span_z scales with |z|, so the condition is the same
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 22, Lemma 26

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_Machine

namespace StackingStars.Main

open MatMulTimeLP

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 22 (PDF 24), Lemma 26. One admissible deterministic real-RAM program `A`, one exponent `k`
and one universal `K`: on the encoding of every list of `n ≥ 1` stars, `A` halts within `N^k + k`
steps and writes, for each star `i`, a translation `(out (3i), out (3i+1))` and a mini-container
label `out (3i+2)`. The mini-container of a label is the convex hull of its translated stars
(the least convex container holding them). Stars with a common label have pairwise disjoint
interiors; the total area of the mini-containers is at most `K (1 + log n) OPT_trans(P)`; and
every mini-container `B` satisfies (16) `span_z(B) ≤ K span_z(P)` for every unit direction `z`
and every star `P` it contains. -/
theorem lemma_26 :
    ∃ (A : Program) (k : ℕ) (K : ℝ), FewInnerTSP.Admissible A ∧ 0 < K ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      RunsWithin A (polysInput P) (polyBound k (totalVerts P)) fun out =>
        (∀ i i' : Fin n, i ≠ i' → out (3 * i + 2) = out (3 * i' + 2) →
          Disjoint (interior (translate (blockTransl 3 out i) (region (P i))))
            (interior (translate (blockTransl 3 out i') (region (P i'))))) ∧
        (∑ ℓ ∈ Finset.univ.image (fun i : Fin n => out (3 * i + 2)),
            hullArea (⋃ j ∈ {j : Fin n | out (3 * j + 2) = ℓ},
              translate (blockTransl 3 out j) (region (P j))) ≤
          K * (1 + Real.log n) * optTrans (fun i => region (P i))) ∧
        ∀ (i : Fin n) (z : Pt), len z = 1 →
          spanIn z (convexHull ℝ (⋃ j ∈ {j : Fin n | out (3 * j + 2) = out (3 * i + 2)},
              translate (blockTransl 3 out j) (region (P j)))) ≤
            K * spanIn z (translate (blockTransl 3 out i) (region (P i))) := by sorry

end StackingStars.Main
