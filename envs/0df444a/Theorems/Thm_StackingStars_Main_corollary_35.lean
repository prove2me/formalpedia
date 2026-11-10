-- Prove2me | Theorems.Thm_StackingStars_Main_corollary_35
-- name    : StackingStars.Main.corollary_35
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:53.256036+00:00
-- url     : https://prove2.me/theorems/1893ad85-e29b-4e4a-8dee-ce937182012b
-- title:
--   Corollary 35 — aligning all radii horizontally costs a universal factor κ′ per size group
-- statement:
--   Let $G=(P_1,\dots,P_n)$ be stars with reference data in the size group with scales $r,w>0$. Let $\widehat G$ be obtained by rotating each star (proper rotation about the origin) so that its radius vector $e_P$ points in the positive horizontal direction. There is a universal constant $\kappa'$ such that
--   $$\mathrm{OPT}_{\mathrm{rot}}(G)\ \le\ \mathrm{OPT}_{\mathrm{trans}}(\widehat G)\ \le\ \kappa'\,\mathrm{OPT}_{\mathrm{rot}}(G).$$
--   The algorithmic consequence is explicit: one admissible real-RAM program, with one polynomial exponent fixed before the instance, takes the scales, stars and reference data, rotates each radius to the right, and returns translations and mini-container labels. Stars of one label have disjoint interiors and the sum of the convex-hull areas of the label classes is at most $\kappa'\,\mathrm{OPT}_{\mathrm{rot}}(G)$. This is how the rotational half of Theorem 1 reduces to the translational one.
--
--   Differences from the source:
--   - generalization: a size group G of an instance → any stars with r_P ∈ (r/2, r], w_P ∈ (w/2, w] for some r, w > 0; reason: every size group satisfies this
--   - encoding: rotating each star so that its radius vector points in the positive horizontal direction → the pose (e₁, −e₂, 0, 0), which maps e_P to (1, 0); reason: the rotation is determined up to translation, which changes no OPT
--   - reading: minimum area of a convex container → the infimum (optTrans, optRot); reason: p. 11 defines OPT as an infimum; attainment is not used
--   - encoding: the common per-group translational algorithm applies to the aligned group with only constant additional loss → a uniform program on groupInput outputs translations and labels for the aligned stars, with total convex-hull area at most κ′ OPT_rot(G); reason: this is the cost consequence of applying Lemma 20 and OPT′ ≤ OPT_trans to the displayed inequality; convex hulls are the least convex mini-containers, and constants can be enlarged together
--   - encoding: the reference data chosen arbitrarily → universally quantified; reason: the paper choices are arbitrary
--   - reading: the per-group algorithm of the preceding section → an admissible deterministic real-RAM program taking the group scales and reference data, halting within N^k + k steps; reason: the same model and input convention as Lemma 20; alignment is computed by field operations and square roots
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 29, Corollary 35

import Mathlib
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData
import Definitions.Def_StackingStars_Main_Machine

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 29 (PDF 31), Corollary 35. For stars `P i` of the size group with scales `r, w`, let `Ĝ` rotate
each star about the origin by the proper rotation `(a, b) = (e₁, −e₂)` taking its radius vector
`e_P` to the positive horizontal direction `(1, 0)`. Then
`OPT_rot(G) ≤ OPT_trans(Ĝ) ≤ κ′ OPT_rot(G)` for one universal `κ′`.
The algorithmic consequence is included: a uniform polynomial-time program on the group input
outputs translations and mini-container labels for these horizontally aligned stars, with total
convex-hull area at most `κ′ OPT_rot(G)`. -/
theorem corollary_35 :
    ∃ (κ' : ℝ) (A : MatMulTimeLP.Program) (k : ℕ), 0 < κ' ∧ FewInnerTSP.Admissible A ∧
      ∀ (n : ℕ) (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ (D : ∀ i, RefData (region (P i))) (r w : ℝ), 0 < r → 0 < w →
      (∀ i, (D i).InGroup r w) →
        optRot (fun i => region (P i)) ≤
          optTrans (fun i => (PolygonPack.Pose.act ⟨(D i).e.1, -(D i).e.2, 0, 0⟩) ''
            region (P i)) ∧
        optTrans (fun i => (PolygonPack.Pose.act ⟨(D i).e.1, -(D i).e.2, 0, 0⟩) ''
            region (P i)) ≤ κ' * optRot (fun i => region (P i)) ∧
        RunsWithin A (groupInput r w P D) (polyBound k (totalVerts P)) (fun out =>
          let placed := fun i : Fin n => translate (blockTransl 3 out i)
            ((PolygonPack.Pose.act ⟨(D i).e.1, -(D i).e.2, 0, 0⟩) '' region (P i))
          (∀ i j : Fin n, i ≠ j → out (3 * i + 2) = out (3 * j + 2) →
            Disjoint (interior (placed i)) (interior (placed j))) ∧
          (∑ ℓ ∈ Finset.univ.image (fun i : Fin n => out (3 * i + 2)),
            hullArea (⋃ j ∈ {j : Fin n | out (3 * j + 2) = ℓ}, placed j)) ≤
              κ' * optRot (fun i => region (P i))) := by sorry

end StackingStars.Main
