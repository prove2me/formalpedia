-- Prove2me | Theorems.Thm_PolygonPack_Supplement_theorem_H_4
-- name    : PolygonPack.Supplement.theorem_H_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:16:30.867118+00:00
-- url     : https://prove2.me/theorems/98d41e33-94f0-411d-ad5d-d2a2ceb88ade
-- title:
--   Theorem H.4 — a margin in one coordinate: $O(1+\log(1/\delta))$-approximations by translations
-- statement:
--   Fix the orientation of every polygon; only translations are allowed. There are an absolute constant $C$ and two functions $f_k$ (knapsack) and $f_b$ (bin packing), each computed by a deterministic Turing machine in time polynomial in the binary length of its input, such that for every $0<\delta<1$ the following hold.
--
--   1. Let $P_0,\dots,P_{n-1}$ be convex polygons with rational vertices and nonnegative rational profits $\pi_i$, each fitting in the unit square by a translation and each of width or height at most $1-\delta$. Then $f_k$ returns rational translations that pack a selected set of the polygons in the unit square, and its profit $V$ satisfies
--   $$\pi(S')\le C\bigl(1+\log(1/\delta)\bigr)\,V$$
--   for every set $S'$ of the polygons that can be packed in the unit square by translations.
--   2. Let $P_0,\dots,P_{n-1}$ be such polygons (without profits). Then $f_b$ returns rational translations packing every polygon exactly once into $N$ unit squares, and
--   $$N\le C\bigl(1+\log(1/\delta)\bigr)\,K$$
--   for every $K$ such that the polygons can be distributed over $K$ unit squares by translations.
--
--   This is the paper's translation-only result under a margin in one coordinate; it is the step that Theorem 1.3 applies after compressing one coordinate.
--
--   Differences from the source:
--   - reading: deterministic polynomial-time algorithms for knapsack and for bin packing → two functions fk, fb with Nonempty (Turing.TM2ComputableInPolyTime …), chosen before δ; reason: p.77: the algorithm never reads δ ("constructs only nonempty scales"; "even an exponentially small margin does not prevent polynomial-time grouping"); the uniform reading is the paper's and the stronger one
--   - encoding: O(1 + log(1/δ))-approximation → one absolute constant C, chosen before δ and the machines, and the factor C·(1 + Real.log (1/δ)); reason: the standard meaning of the O(·); the proof gives (44 + 108m)K and (44 + 108m)/(1 − τ), m = max{0, ⌈log₂(1/δ)⌉ − 2}, pp.77–78
--   - encoding: the optimum of knapsack and of bin packing by translations → π(S') for every translation-feasible S', and every assignment to K unit squares with translation-feasible parts; reason: equivalent to a bound by the optimum; K = 0 covers the empty instance ("An empty instance uses zero bins", p.77)
--   - reading: weighted knapsack → nonnegative rational profits; reason: §1, p.1: "each polygon Pi has a nonnegative rational profit"
--   - reading: algorithms by translations → rational output translations (TOut, TBins), real comparator translations; reason: p.78: "exact rational translations"; the comparator is any feasible packing
--   - reading: width or height of a polygon → the coordinate spans of its vertex list; reason: they equal the spans of the convex hull
--   - generalization: positive-area polygons (p.74: "We work with positive-area polygons") → polygons of any area, including points and segments; reason: p.74 extends the result to degenerate polygons explicitly; the statement specializes to positive-area ones
--   - generalization: convex polygons given by their rational vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem H.4, p.77 (PDF p.78); proof pp.77–78 (PDF pp.78–79)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_encOut
import Definitions.Def_PolygonPack_Supplement_TPacks
import Definitions.Def_PolygonPack_Supplement_TOut
import Definitions.Def_PolygonPack_Supplement_encTOut
import Definitions.Def_PolygonPack_Supplement_span

namespace PolygonPack.Supplement

open PolygonPack

/-- **Theorem H.4 (A margin in one coordinate).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem H.4, p.77 (PDF p.78); proof pp.77–78. "Suppose each polygon individually fits in a unit square and has width or height at most 1 − δ, where 0 < δ < 1. Weighted knapsack and absolute bin packing by translations in unit squares have deterministic polynomial-time O(1 + log(1/δ))-approximations."

There are an absolute constant `C` and two functions computed by polynomial-time Turing machines, `fk` for
knapsack and `fb` for bin packing, such that for every `0 < δ < 1`:
1. on every instance with nonnegative profits whose polygons each fit the unit square by a translation and have
   width or height at most `1 − δ`, `fk` returns rational translations packing a selected set in the unit square,
   and `π(S') ≤ C(1 + log(1/δ))·π(output)` for every set `S'` that can be packed by translations in the unit square;
2. on every such list of polygons, `fb` returns rational translations packing every polygon exactly once into unit
   squares, using at most `C(1 + log(1/δ))·K` squares whenever the polygons can be distributed over `K` unit
   squares by translations.

**Formalization Note.** The machines do not depend on `δ`: the paper's algorithm never reads `δ` (p.77: "The
algorithm constructs only nonempty scales", "even an exponentially small margin does not prevent
polynomial-time grouping"); `C` comes before everything, so the `O(·)` is a genuine absolute constant. Time is
`Turing.TM2ComputableInPolyTime` on the fixed binary encoders `encInstance`, `encPolys`, `encTOut`, `encTBins`.
Comparators use real translations, outputs rational ones (p.78). The bin bound is absolute (no additive term;
`K = 0` forces zero bins). Positive area is not assumed (p.74 covers degenerate polygons). -/
theorem theorem_H_4 :
    ∃ C : ℝ, ∃ fk : Instance → TOut, ∃ fb : List (List (ℚ × ℚ)) → TBins,
      Nonempty (Turing.TM2ComputableInPolyTime encInstance encTOut fk) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encPolys encTBins fb) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        (∀ I : Instance, (∀ P ∈ I, FitsT P.1 ∧ HasMargin δ P.1 ∧ 0 ≤ P.2) →
          (fk I).Sound I unitSq ∧
            ∀ S' : Finset (Fin I.n), TFeasible I S' →
              profit I S' ≤ C * (1 + Real.log (1 / δ)) * profit I ((fk I).indexSet I)) ∧
        (∀ l : List (List (ℚ × ℚ)), (∀ v ∈ l, FitsT v ∧ HasMargin δ v) →
          (fb l).Sound (Instance.ofPolys l) unitSq ∧
            ∀ (K : ℕ) (g : Fin (Instance.ofPolys l).n → Fin K),
              (∀ k : Fin K, TFeasible (Instance.ofPolys l) (Finset.univ.filter (fun i => g i = k))) →
                ((fb l).length : ℝ) ≤ C * (1 + Real.log (1 / δ)) * K) := by sorry

end PolygonPack.Supplement
