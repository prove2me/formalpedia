-- Prove2me | Theorems.Thm_StackingStars_Main_theorem_5
-- name    : StackingStars.Main.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:31.745193+00:00
-- url     : https://prove2.me/theorems/d6d1ad0a-26ae-4023-9120-53abe467ac39
-- title:
--   Theorem 5 (Alt–de Berg–Knauer) — O(N log N)-time packing of convex polygons into a rectangle of area O(Σ|C_i| + ℓ_max h_max)
-- statement:
--   There are an admissible deterministic real-RAM program $A$ and a constant $c>0$ with the following property. Let $C_1,\dots,C_n$ ($n\ge1$) be convex polygons of total complexity $N$, that is, $N$ vertices in all, given by their vertex lists. On this input $A$ halts within $c\,N(1+\log N)$ steps and outputs a translation of each $C_i$ together with an axis-aligned rectangle $R$. The translated polygons have pairwise disjoint interiors, lie in $R$, and
--   $$|R|\ \le\ c\cdot\Bigl(\sum_{i=1}^n|C_i|+\ell_{\max}h_{\max}\Bigr),$$
--   where $\ell_{\max}$ and $h_{\max}$ are the largest horizontal and vertical spans of $C_1,\dots,C_n$. The result is cited from Alt, de Berg and Knauer (Theorem 2.2 of [AdBK17, AdBK20]). It packs the mini-containers in Theorem 27 and in the rotational half of Theorem 1.
--
--   Differences from the source:
--   - reading: an O(N log N)-time algorithm → an admissible program of the published real RAM halting within c · N · (1 + log N) steps on every valid input; reason: the paper names no model; 1 + log N keeps the bound positive at N = 1 and agrees with N log N up to a constant for N ≥ 2
--   - encoding: two constants (time and area c) → one constant c for both; reason: the larger of the two works for both clauses
--   - encoding: convex polygons C_1, …, C_n → vertex lists of simple polygons with convex closed regions, n ≥ 1; reason: a convex polygon is given by its vertices; for n = 0 there is nothing to pack
--   - encoding: the output (translations and rectangle R) → translations (out(2i), out(2i+1)) followed by R = [out(2n), out(2n+2)] × [out(2n+1), out(2n+3)]; reason: a machine statement needs a layout
--   - encoding: packing → pairwise disjoint interiors of the translated polygons, which lie in R; reason: the paper notion of packing
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 3, Theorem 5 (Theorem 2.2 from Alt, de Berg, Knauer)

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
p. 3 (PDF 5), Theorem 5 (Theorem 2.2 of Alt, de Berg, Knauer): an `O(N log N)`-time algorithm
packing convex polygons `C_1, …, C_n` of total complexity `N` by translations into an
axis-aligned rectangle `R` with `|R| ≤ c (Σ_i |C_i| + ℓ_max h_max)`, `ℓ_max`, `h_max` the maximum
horizontal and vertical spans. One admissible deterministic real-RAM program `A` and one constant
`c`: on the encoding of every list of `n ≥ 1` convex polygons, `A` halts within
`c · N · (1 + log N)` steps and writes the translations `(out (2i), out (2i+1))` and then the
rectangle `R = [out (2n), out (2n+2)] × [out (2n+1), out (2n+3)]`; the translated polygons have
pairwise disjoint interiors and lie in `R`, and `|R| ≤ c (Σ |C_i| + ℓ_max h_max)`. -/
theorem theorem_5 :
    ∃ (A : Program) (c : ℝ), FewInnerTSP.Admissible A ∧ 0 < c ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsConvexPolygon (P i)) →
      RunsWithin A (polysInput P)
          (c * (totalVerts P : ℝ) * (1 + Real.log (totalVerts P))) fun out =>
        IsPacking (fun i : Fin n => translate (blockTransl 2 out i) (region (P i))) ∧
        (∀ i : Fin n, translate (blockTransl 2 out i) (region (P i)) ⊆ outAxisRect out (2 * n)) ∧
        area (outAxisRect out (2 * n)) ≤
          c * (∑ i, area (region (P i)) +
            (⨆ i, spanIn (1, 0) (region (P i))) * (⨆ i, spanIn (0, 1) (region (P i)))) := by sorry

end StackingStars.Main
