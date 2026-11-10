-- Prove2me | Theorems.Thm_StackingStars_Main_theorem_27
-- name    : StackingStars.Main.theorem_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:31.245175+00:00
-- url     : https://prove2.me/theorems/da80864e-8156-4497-9d95-ddd91182d6e3
-- title:
--   Theorem 27 — polynomial-time translational packing of stars into a rectangle of area O(log n) · OPT
-- statement:
--   There are an admissible deterministic real-RAM program $A$, an exponent $k$ and a universal constant $K$ with the following property. On the encoding of every list of $n\ge1$ stars $P$, $A$ halts within $N^k+k$ steps, where $N$ is the total number of vertices. It outputs a translation of each star and a rectangle $B=\{p+sf+tg: s,t\in[0,1]\}$ with $f\cdot g=0$. The translated stars have pairwise disjoint interiors, lie in $B$, and
--   $$|B|\ \le\ K\,(1+\log n)\,\mathrm{OPT}_{\mathrm{trans}}(P).$$
--   This is the translational half of Theorem 1, with a rectangle as the container.
--
--   Differences from the source:
--   - reading: in polynomial time, we can compute → an admissible program of the published real RAM halting within N^k + k steps, k fixed before the input; reason: the paper names no model and its coordinates are real
--   - reading: O(log n) → K · (1 + log n) with one universal K; reason: log 1 = 0 at n = 1
--   - encoding: a rectangle (any orientation) → {p + s f + t g : s, t ∈ [0, 1]} with f · g = 0, written after the translations; reason: every rectangle has this form; a degenerate one changes nothing since it must contain the stars
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 22, Theorem 27

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
p. 22 (PDF 24), Theorem 27: "For a set of stars P, in polynomial time, we can compute a packing
of P into a rectangle of area O(log n) · OPT(P)." One admissible deterministic real-RAM program
`A`, one exponent `k` and one universal `K`: on the encoding of every list of `n ≥ 1` stars, `A`
halts within `N^k + k` steps and writes the translations `(out (2i), out (2i+1))` and then a
rectangle `{p + s f + t g : s, t ∈ [0, 1]}` with `p = (out (2n), out (2n+1))`,
`f = (out (2n+2), out (2n+3))`, `g = (out (2n+4), out (2n+5))`, `f · g = 0`; the translated stars
have pairwise disjoint interiors and lie in the rectangle, whose area is at most
`K (1 + log n) OPT_trans(P)`. -/
theorem theorem_27 :
    ∃ (A : Program) (k : ℕ) (K : ℝ), FewInnerTSP.Admissible A ∧ 0 < K ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      RunsWithin A (polysInput P) (polyBound k (totalVerts P)) fun out =>
        IsPacking (fun i : Fin n => translate (blockTransl 2 out i) (region (P i))) ∧
        dot (out (2 * n + 2), out (2 * n + 3)) (out (2 * n + 4), out (2 * n + 5)) = 0 ∧
        (∀ i : Fin n, translate (blockTransl 2 out i) (region (P i)) ⊆
          rect (out (2 * n), out (2 * n + 1)) (out (2 * n + 2), out (2 * n + 3))
            (out (2 * n + 4), out (2 * n + 5)) 1 1) ∧
        area (rect (out (2 * n), out (2 * n + 1)) (out (2 * n + 2), out (2 * n + 3))
            (out (2 * n + 4), out (2 * n + 5)) 1 1) ≤
          K * (1 + Real.log n) * optTrans (fun i => region (P i)) := by sorry

end StackingStars.Main
