-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_23
-- name    : StackingStars.Main.lemma_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:44:39.071797+00:00
-- url     : https://prove2.me/theorems/b9984748-16a0-4da6-a9cf-9089b0f5439c
-- title:
--   Lemma 23 — the stars of a size group whose cores meet K_P fit in one O(r) × O(w) rectangle
-- statement:
--   Let $P_1,\dots,P_n$ be stars with reference data in the size group with scales $r,w>0$, placed as a packing. There is a universal constant $K$ such that for every star $P=P_i$ some rectangle with side lengths at most $Kr$ and $Kw$ contains every placed star $P'$ whose core meets the core of $P$:
--   $$\{P':\ K_{P'}\cap K_P\neq\emptyset\}\ \subseteq\ B,\qquad B\ \text{an }O(r)\times O(w)\text{ rectangle}.$$
--   The rectangle may have any orientation. Together with Lemma 22 this gives the upper bound (15) in the proof of Lemma 24.
--
--   Differences from the source:
--   - generalization: stars of a size group in a (translational) packing → stars placed by rigid poses forming a packing; reason: translations are poses with a = 1, b = 0
--   - reading: the packing is implicit in the printed statement → an explicit hypothesis that the placed stars have pairwise disjoint interiors; reason: the proof uses that radii of different stars cannot cross, which holds only in a packing
--   - generalization: a size group G_{a,b} of an instance → any r, w > 0 with r_P ∈ (r/2, r], w_P ∈ (w/2, w]; reason: every size group satisfies this
--   - encoding: an O(r) × O(w) rectangle → rect p f g a b with f, g orthonormal and a ≤ K r, b ≤ K w, K universal; reason: asymptotic notation made explicit
--   - encoding: the reference data chosen arbitrarily → universally quantified; reason: the paper choices are arbitrary
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 21, Lemma 23

import Mathlib
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 21 (PDF 23), Lemma 23: "Let P be a star in the size group with scales r and w. There is an
O(r) × O(w) rectangle that contains all stars P′ in the same group such that K_{P′} ∩ K_P ≠ ∅."
One universal `K`: for every packing (by rigid poses; translations included) of stars of the size
group with scales `r, w` and every star `i`, some rectangle with orthonormal side directions
`f, g` and side lengths at most `K r`, `K w` contains every placed star `j` whose placed core
meets the placed core of `i`. -/
theorem lemma_23 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ (D : ∀ i, RefData (region (P i))) (r w : ℝ), 0 < r → 0 < w →
      (∀ i, (D i).InGroup r w) →
      ∀ T : Fin n → PolygonPack.Pose, (∀ i, (T i).IsRigid) →
      IsPacking (fun i => (T i).act '' region (P i)) →
      ∀ i, ∃ (p f g : Pt) (a b : ℝ), len f = 1 ∧ len g = 1 ∧ dot f g = 0 ∧
        0 ≤ a ∧ a ≤ K * r ∧ 0 ≤ b ∧ b ≤ K * w ∧
        ∀ j, ((T j).act '' (D j).core ∩ (T i).act '' (D i).core).Nonempty →
          (T j).act '' region (P j) ⊆ rect p f g a b := by sorry

end StackingStars.Main
