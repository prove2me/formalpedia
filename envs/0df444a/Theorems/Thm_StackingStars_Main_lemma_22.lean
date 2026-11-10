-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_22
-- name    : StackingStars.Main.lemma_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:44:30.235891+00:00
-- url     : https://prove2.me/theorems/a95550d9-d60c-4b4e-9f0f-3b03a25574f5
-- title:
--   Lemma 22 — cores of a long thin star and a short fat star are disjoint in any packing
-- statement:
--   Recall the core $K_P$ of a star $P$, the triangle $\triangle q'_PR'_PL'_P$ with $q'_P=(q_P+R_P)/2+w_Pv_P/10$, $R'_P=q'_P+(R_P-q_P)/10$ and $L'_P=q'_P+(L_P-q_P)/10$. Let $P_1,P_2$ be two stars with reference data such that
--   $$r_{P_1}>10\,r_{P_2}\qquad\text{and}\qquad w_{P_2}>10\,w_{P_1}.$$
--   In any packing, meaning any placement of $P_1,P_2$ by rigid motions with disjoint interiors, the placed cores are disjoint: $K_{P_1}\cap K_{P_2}=\emptyset$. The disjoint cores give the area lower bound behind Lemma 24 and Corollary 25.
--
--   Differences from the source:
--   - generalization: in any packing (translations, §3) → any placement of the two stars by rigid poses with disjoint interiors, cores moved with their stars; reason: translations are the poses with a = 1, b = 0, so this specializes to the printed statement
--   - encoding: q_P, R_P, L_P chosen arbitrarily → universally quantified over every admissible choice; reason: the paper choices are arbitrary; the statement holds for each
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 20, Lemma 22

import Mathlib
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_ReferenceData

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 20 (PDF 22), Lemma 22: "Let P1, P2 be two stars such that r_{P1} > 10 r_{P2} and
w_{P2} > 10 w_{P1}. In any packing, K_{P1} ∩ K_{P2} = ∅." Stated for every admissible choice of
reference data and every packing by rigid poses (rotations and translations; translations are the
case `a = 1, b = 0`); the cores move with their stars. -/
theorem lemma_22 (V₁ V₂ : List Pt) (h₁ : IsStarPolygon V₁) (h₂ : IsStarPolygon V₂)
    (D₁ : RefData (region V₁)) (D₂ : RefData (region V₂))
    (hr : D₁.r > 10 * D₂.r) (hw : D₂.w > 10 * D₁.w)
    (T₁ T₂ : PolygonPack.Pose) (hT₁ : T₁.IsRigid) (hT₂ : T₂.IsRigid)
    (hpack : Disjoint (interior (T₁.act '' region V₁)) (interior (T₂.act '' region V₂))) :
    Disjoint (T₁.act '' D₁.core) (T₂.act '' D₂.core) := by sorry

end StackingStars.Main
