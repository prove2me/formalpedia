-- Prove2me | Theorems.Thm_StackingStars_Main_theorem_1
-- name    : StackingStars.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:45.89039+00:00
-- url     : https://prove2.me/theorems/350df202-0d47-416e-bc08-d9c0369949c6
-- title:
--   Theorem 1 — polynomial-time O(log n)-approximation for translational and rotational minimum-area convex-container packing of star-shaped polygons
-- statement:
--   A star is a simple polygon, given by its list of vertices with real coordinates, whose closed region contains a point that sees the whole region. For a list $P=(P_1,\dots,P_n)$ of stars, $\mathrm{OPT}_{\mathrm{trans}}(P)$ and $\mathrm{OPT}_{\mathrm{rot}}(P)$ are the infimum areas of a convex container (equivalently, of the convex hull of the placed polygons) over all placements by translations, respectively by rigid motions (a proper rotation followed by a translation), in which the polygons have pairwise disjoint interiors.
--
--   There are a universal constant $C$, an exponent $k$, and two admissible deterministic real-RAM programs $A_{\mathrm{trans}}$ and $A_{\mathrm{rot}}$ with the following property. For every list of $n\ge1$ stars with $N$ vertices in total, each program halts within $N^k+k$ steps.
--
--   * $A_{\mathrm{trans}}$ outputs a translation vector per star. The translated stars have pairwise disjoint interiors, and their convex hull has area at most $C(1+\log n)\,\mathrm{OPT}_{\mathrm{trans}}(P)$.
--   * $A_{\mathrm{rot}}$ outputs a pose $(a,b,x,y)$ with $a^2+b^2=1$ per star, acting by $z\mapsto(az_1-bz_2+x,\ bz_1+az_2+y)$. The placed stars have pairwise disjoint interiors, and their convex hull has area at most $C(1+\log n)\,\mathrm{OPT}_{\mathrm{rot}}(P)$.
--
--   $$\Bigl|\operatorname{conv}\bigcup_i \text{placed }P_i\Bigr|\ \le\ C\,(1+\log n)\,\mathrm{OPT}.$$
--
--   This is the first polynomial-time $o(n)$-approximation for packing an unbounded number of nonconvex polygons with arbitrary edge orientations. Before it, only convex inputs had such guarantees.
--
--   Differences from the source:
--   - reading: star-shaped polygons → simple polygons given by vertex lists of at least three points with real coordinates, whose closed region has a nonempty kernel; reason: the paper reserves possibly weakly simple for bowls (p. 14) and the proof of Lemma 22 needs a connected interior
--   - reading: polynomial-time algorithms → admissible programs of the published real RAM halting within N^k + k steps on every valid input, k fixed before the input; reason: the paper names no model, its coordinates are real and its Theorem 5 is a real-RAM algorithm
--   - reading: O(log n)-approximation → convex-hull area at most C · (1 + log n) · OPT with one universal C; reason: log 1 = 0 would give a zero area bound; 1 + log n is positive at n = 1 and agrees up to a constant for n ≥ 2
--   - encoding: placing without overlap into a minimum-area convex container → pairwise disjoint interiors; container area = convex-hull area of the union; OPT = infimum over packings; reason: the least convex container of a placed family is its convex hull; p. 11 defines OPT as an infimum
--   - encoding: rotations → PolygonPack.Pose with IsRigid (a² + b² = 1), no reflection; reason: the rotational variant allows rotations and translations only
--   - encoding: input and output → input n, then each polygon vertex count and coordinates; output translations or poses after the input; reason: a machine statement needs a layout
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2, Theorem 1 (proved as Theorem 27, p. 22, and after Lemma 36, p. 30)

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
p. 2 (PDF 4), Theorem 1: "There are polynomial-time O(log n)-approximation algorithms for both
translational and rotational packing of n star-shaped polygons into a minimum-area convex
container." One universal `C`, one exponent `k` and two admissible deterministic real-RAM programs
`A_trans`, `A_rot`: on the encoding of every list of `n ≥ 1` simple star-shaped polygons (real
coordinates, any number of vertices), each halts within `N^k + k` steps (`N` the total number of
vertices). `A_trans` writes a translation `(out (2i), out (2i+1))` per polygon; the translates have
pairwise disjoint interiors and the convex hull of their union has area at most
`C (1 + log n) OPT_trans`. `A_rot` writes a pose `(out (4i), …, out (4i+3))` per polygon, a proper
rotation (`a² + b² = 1`) and a translation; the placed polygons have pairwise disjoint interiors
and the convex hull of their union has area at most `C (1 + log n) OPT_rot`. -/
theorem theorem_1 :
    ∃ (C : ℝ) (k : ℕ) (A_trans A_rot : Program), 0 < C ∧
      FewInnerTSP.Admissible A_trans ∧ FewInnerTSP.Admissible A_rot ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
        RunsWithin A_trans (polysInput P) (polyBound k (totalVerts P)) (fun out =>
          IsPacking (fun i : Fin n => translate (blockTransl 2 out i) (region (P i))) ∧
          hullArea (⋃ i : Fin n, translate (blockTransl 2 out i) (region (P i))) ≤
            C * (1 + Real.log n) * optTrans (fun i => region (P i))) ∧
        RunsWithin A_rot (polysInput P) (polyBound k (totalVerts P)) (fun out =>
          (∀ i : Fin n, (blockPose 4 out i).IsRigid) ∧
          IsPacking (fun i : Fin n => (blockPose 4 out i).act '' region (P i)) ∧
          hullArea (⋃ i : Fin n, (blockPose 4 out i).act '' region (P i)) ≤
            C * (1 + Real.log n) * optRot (fun i => region (P i))) := by sorry

end StackingStars.Main
