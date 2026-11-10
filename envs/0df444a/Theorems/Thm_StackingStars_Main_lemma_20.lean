-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_20
-- name    : StackingStars.Main.lemma_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:52.249823+00:00
-- url     : https://prove2.me/theorems/3862fc3f-1661-4a57-9b60-fbca7d4723ae
-- title:
--   Lemma 20 — polynomial-time packing of one size group into rectangular mini-containers of total area O(OPT′)
-- statement:
--   There are an admissible deterministic real-RAM program $A$, an exponent $k$ and a universal constant $K$ with the following property. Take any list of $n$ stars $P_1,\dots,P_n$ with reference data, all in the size group with scales $r,w>0$, and run $A$ on the input made of $r$, $w$, the stars and their reference points. Then $A$ halts within $N^k+k$ steps, where $N$ is the total number of vertices. It outputs for each star $i$ a translation $t_i$ and a mini-container label $\ell_i$, and these satisfy:
--
--   * stars with a common label have pairwise disjoint interiors after translation;
--   * for every label $\ell$ there is a rectangle $B_\ell$ with sides parallel to $u_\tau,d_\tau$ and lengths at most $Kr$ and $Kw$ that contains the translated stars labelled $\ell$, where $\tau$ is the common fine type of all those stars;
--   * $$\sum_\ell|B_\ell|\ \le\ K\cdot\mathrm{OPT}'(P).$$
--
--   Differences from the source:
--   - reading: one can compute in polynomial time → an admissible program of the published real RAM halting within N^k + k steps on every valid input, k fixed before the input; reason: the paper names no model, its coordinates are real and its Theorem 5 is a real-RAM algorithm
--   - reading: a set of stars in the same size group → the scales r, w and the reference data are part of the input; the statement holds for every admissible choice; reason: the size group and the fine types are defined only relative to the reference data and the scales
--   - generalization: a size group G_{a,b} of an instance → any r, w > 0 with r_P ∈ (r/2, r], w_P ∈ (w/2, w]; reason: every size group satisfies this
--   - encoding: the computed packing into rectangular mini-containers → per star a translation (out(3i), out(3i+1)) and a label out(3i+2); the rectangle of each label exists with the stated sides; reason: a machine statement needs a layout; the least such rectangle is determined by the output
--   - encoding: O(r) × O(w) and O(OPT′(P)) → one universal K; reason: asymptotic notation made explicit
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 19, Lemma 20

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData
import Definitions.Def_StackingStars_Main_FineType
import Definitions.Def_StackingStars_Main_Machine

namespace StackingStars.Main

open MatMulTimeLP

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 19 (PDF 21), Lemma 20. One admissible deterministic real-RAM program `A`, one exponent `k` and
one universal `K`: on the input `groupInput r w P D` (scales, stars, reference data) of every list
of stars in the size group with scales `r, w`, `A` halts within `N^k + k` steps (`N` the total
number of vertices) and writes, for each star `i`, a translation `(out (3i), out (3i+1))` and a
mini-container label `ℓ i = out (3i+2)`. The translated stars with a common label have pairwise
disjoint interiors and share a fine type `τ ℓ`; they lie in a rectangle with sides parallel to
`u_τ`, `d_τ` of dimensions at most `K r × K w`; and the rectangles' total area is at most
`K · OPT′(P)`. -/
theorem lemma_20 :
    ∃ (A : Program) (k : ℕ) (K : ℝ), FewInnerTSP.Admissible A ∧ 0 < K ∧
      ∀ (n : ℕ) (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ (D : ∀ i, RefData (region (P i))) (r w : ℝ), 0 < r → 0 < w →
      (∀ i, (D i).InGroup r w) →
      RunsWithin A (groupInput r w P D) (polyBound k (totalVerts P)) fun out =>
        (∀ i i' : Fin n, i ≠ i' → out (3 * i + 2) = out (3 * i' + 2) →
          Disjoint (interior (translate (blockTransl 3 out i) (region (P i))))
            (interior (translate (blockTransl 3 out i') (region (P i'))))) ∧
        ∃ (τ : ℝ → FineType) (p : ℝ → Pt) (a b : ℝ → ℝ),
          (∀ i : Fin n, HasFineType r w (D i) (τ (out (3 * i + 2))) ∧
            translate (blockTransl 3 out i) (region (P i)) ⊆
              rect (p (out (3 * i + 2))) ((τ (out (3 * i + 2))).u r w)
                ((τ (out (3 * i + 2))).d r w) (a (out (3 * i + 2))) (b (out (3 * i + 2)))) ∧
          (∀ ℓ ∈ Finset.univ.image (fun i : Fin n => out (3 * i + 2)),
            0 ≤ a ℓ ∧ a ℓ ≤ K * r ∧ 0 ≤ b ℓ ∧ b ℓ ≤ K * w) ∧
          ∑ ℓ ∈ Finset.univ.image (fun i : Fin n => out (3 * i + 2)),
              area (rect (p ℓ) ((τ ℓ).u r w) ((τ ℓ).d r w) (a ℓ) (b ℓ)) ≤
            K * optPrime (fun i => region (P i)) := by sorry

end StackingStars.Main
