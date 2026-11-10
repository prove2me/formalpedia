-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_8
-- name    : StackingStars.Main.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:44:19.650127+00:00
-- url     : https://prove2.me/theorems/60050786-4ee4-41e7-869f-c4226b00b928
-- title:
--   Lemma 8 — OPT = Ω(r_max · w_max)
-- statement:
--   For a list of stars $P$ and any choice of reference data, let $r_{\max}=\max_Pr_P$ be the largest radius length and $w_{\max}=\max_Pw_P$ the largest width. There is a universal constant $c>0$ such that for every list of $n\ge1$ stars and every admissible choice of reference data
--   $$\mathrm{OPT}_{\mathrm{rot}}(P)\ \ge\ c\,r_{\max}\,w_{\max}.$$
--   Since every translational packing is a rotational one, $\mathrm{OPT}_{\mathrm{trans}}(P)\ge\mathrm{OPT}_{\mathrm{rot}}(P)$, and the bound holds for the translational optimum as well. The lemma bounds the cost of the stars that are packed individually (Lemma 26, Lemma 36) and the term $\ell_{\max}h_{\max}$ of Theorem 5.
--
--   Differences from the source:
--   - generalization: OPT(P), the translational optimum of §3 → OPT_rot(P); reason: OPT_rot ≤ OPT_trans, so the Lean bound implies the printed one; the paper uses the rotational form on p. 30
--   - encoding: Ω(r_max w_max) → c · r_max · w_max with one universal c > 0 fixed before the instance; reason: asymptotic notation made explicit
--   - encoding: reference data q_P, R_P, L_P chosen arbitrarily → universally quantified over every admissible choice; reason: the paper choices are arbitrary, so the statement holds for each
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 12, Lemma 8

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 12 (PDF 14), Lemma 8: "For a set of stars P, OPT(P) = Ω(r_max w_max)." One universal `c > 0`:
for every nonempty list of stars and every admissible choice of reference data,
`OPT_rot ≥ c · r_max · w_max` (hence also `OPT_trans ≥ c · r_max · w_max`, since every
translational packing is a rotational one). -/
theorem lemma_8 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ D : ∀ i, RefData (region (P i)),
        c * rMax D * wMax D ≤ optRot (fun i => region (P i)) := by sorry

end StackingStars.Main
