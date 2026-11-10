-- Prove2me | Theorems.Thm_StackingStars_Main_corollary_25
-- name    : StackingStars.Main.corollary_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:44:34.924675+00:00
-- url     : https://prove2.me/theorems/15aaa44a-529a-4c34-aa29-9ecdc75e1eca
-- title:
--   Corollary 25 — Σ over size groups of OPT′(G) = O(log n) · OPT(P)
-- statement:
--   For a list of $n\ge1$ stars with reference data, the size group $G_{a,b}$ consists of the stars with $r_P\in(r_{\max}/2^{a+1},r_{\max}/2^a]$ and $w_P\in(w_{\max}/2^{b+1},w_{\max}/2^b]$. There is a universal constant $K$ such that
--   $$\sum_{G:\ \text{size group}}\mathrm{OPT}'(G)\ \le\ K\,(1+\log n)\,\mathrm{OPT}(P),$$
--   where $\mathrm{OPT}=\mathrm{OPT}_{\mathrm{trans}}$ and the sum runs over the nonempty size groups. Packing each size group separately therefore loses only a logarithmic factor, not the $\log^2n$ that the number of size groups suggests.
--
--   Differences from the source:
--   - reading: O(log n) → K · (1 + log n) with one universal K; reason: log 1 = 0; the two agree up to a constant for n ≥ 2
--   - encoding: the sum over size groups G → the sum over the image of groupIdx (the nonempty groups G_{a,b}); reason: empty groups have OPT′ = 0
--   - encoding: the reference data chosen arbitrarily → universally quantified; reason: the paper choices are arbitrary
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 22, Corollary 25

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 22 (PDF 24), Corollary 25: "For a set of stars P, Σ_{G: size group} OPT′(G) = O(log n) · OPT(P)."
One universal `K`: for every list of `n ≥ 1` stars and every admissible choice of reference data,
the sum over the nonempty size groups `G_{a,b}` (`groupIdx`) of `OPT′(G)` is at most
`K (1 + log n) OPT_trans(P)`. -/
theorem corollary_25 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ D : ∀ i, RefData (region (P i)),
        ∑ g ∈ Finset.univ.image (groupIdx D),
            optPrime (fun i : {i : Fin n // groupIdx D i = g} => region (P i)) ≤
          K * (1 + Real.log n) * optTrans (fun i => region (P i)) := by sorry

end StackingStars.Main
