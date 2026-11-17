-- Prove2me | Theorems.Thm_PolygonPack_Supplement_theorem_1_3
-- name    : PolygonPack.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:15:46.358021+00:00
-- url     : https://prove2.me/theorems/968fcffb-9869-48d0-8de2-7480ebb4e64e
-- title:
--   Theorem 1.3 — $O(1+\log(1/\varepsilon))$-approximations for translation knapsack and bin packing with $(1+\varepsilon)$ width augmentation
-- statement:
--   Fix the orientation of every polygon; only translations are allowed. There is an absolute constant $C$ such that for every real $0<\varepsilon<1$ there are two functions $f_k$ (knapsack) and $f_b$ (bin packing), each computed by a deterministic Turing machine in time polynomial in the binary length of its input, with the following properties.
--
--   1. Let $P_0,\dots,P_{n-1}$ be convex polygons with rational vertices and nonnegative rational profits. Then $f_k$ returns rational translations that pack a selected set of the polygons in the rectangle $[0,1+\varepsilon]\times[0,1]$, and its profit $V$ satisfies
--   $$\pi(S')\le C\bigl(1+\log(1/\varepsilon)\bigr)\,V$$
--   for every set $S'$ of the polygons that can be packed in the unit square by translations.
--   2. Let $P_0,\dots,P_{n-1}$ be convex polygons with rational vertices, each fitting in the unit square by a translation. Then $f_b$ returns rational translations packing every polygon exactly once into $N$ rectangles $[0,1+\varepsilon]\times[0,1]$, and
--   $$N\le C\bigl(1+\log(1/\varepsilon)\bigr)\,K$$
--   for every $K$ such that the polygons can be distributed over $K$ unit squares by translations.
--
--   This is the paper's resource-augmentation guarantee for translation-only packing: widening the container by a factor $1+\varepsilon$ in one coordinate gives logarithmic approximations for both knapsack and bin packing.
--
--   Differences from the source:
--   - reading: one-dimensional (1+ε)-resource augmentation → width augmentation: outputs in the box [0, 1+ε] × [0, 1], comparators in the unit square; reason: the version App. H.5 proves; the height version is the remark "Exchanging coordinates gives the corresponding guarantee" (p.78)
--   - reading: approximation algorithms for packing (Theorem 1.3, in §1.1 under "Packing with translations only") → translations only: rational output translations, real comparator translations; reason: App. H, p.74 "Fix the orientation of every input polygon"; p.78 "exact rational translations"
--   - reading: deterministic polynomial-time algorithms for weighted knapsack and bin packing → two functions fk, fb with Nonempty (Turing.TM2ComputableInPolyTime …), chosen after ε; reason: H.5 compresses by 1/(1+ε), so the machine may depend on ε; time in binary input length, p.78
--   - encoding: O(1 + log(1/ε))-approximation → one absolute constant C, chosen before ε, and the factor C·(1 + Real.log (1/ε)); reason: the standard meaning of the O(·); H.5 gives it from Theorem H.4 with δ = ε/(1+ε) ≥ ε/2
--   - encoding: every fixed 0 < ε < 1 → every real ε with 0 < ε < 1; reason: H.5, p.78: "For fixed real ε, use a fixed rational ε′ ∈ [ε/2, ε] instead"
--   - reading: weighted knapsack → nonnegative rational profits and no fit hypothesis; reason: §1, p.1 (nonnegative rational profits); p.74: an item that does not fit "can be discarded for knapsack"
--   - reading: bin packing → every polygon fits the unit square by a translation; reason: p.74: an item that fails this test "makes a bin-packing instance infeasible"
--   - encoding: the optimum of knapsack and of bin packing → π(S') for every translation-feasible S', and every assignment to K unit squares with translation-feasible parts; reason: equivalent to a bound by the optimum; K = 0 covers the empty instance
--   - generalization: positive-area polygons (p.74: "We work with positive-area polygons") → polygons of any area, including points and segments; reason: p.74 extends the result to degenerate polygons explicitly; the statement specializes to positive-area ones
--   - generalization: convex polygons given by their rational vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.3, p.4 (PDF p.5); proof App. H.5, p.78 (PDF p.79)

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

/-- **Theorem 1.3.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.3, p.4 (PDF p.5); proof App. H.5, p.78 (PDF p.79). "For every fixed 0 < ε < 1, there are deterministic polynomial-time O(1 + log(1/ε))-approximation algorithms for weighted knapsack and bin packing under one-dimensional (1+ε)-resource augmentation."

There is an absolute constant `C` such that for every real `0 < ε < 1` there are two functions computed by
polynomial-time Turing machines, `fk` for knapsack and `fb` for bin packing, with:
1. on every instance with nonnegative profits, `fk` returns rational translations packing a selected set in the
   box `[0, 1+ε] × [0, 1]`, and `π(S') ≤ C(1 + log(1/ε))·π(output)` for every set `S'` that can be packed by
   translations in the unit square;
2. on every list of polygons each fitting the unit square by a translation, `fb` returns rational translations
   packing every polygon exactly once into boxes `[0, 1+ε] × [0, 1]`, using at most `C(1 + log(1/ε))·K` boxes
   whenever the polygons can be distributed over `K` unit squares by translations.

**Formalization Note.** The augmentation is in the width, the version App. H.5 proves; the paper's height
version is a remark ("Exchanging coordinates gives the corresponding guarantee"). The machines come after `ε`
(H.5 compresses by `1/(1+ε)`), `C` before it. Comparators are unaugmented unit squares with real translations;
outputs are rational translations into the augmented box (p.78). Knapsack needs no fit hypothesis (oversized
items are discarded, p.74). The bin bound is absolute (`K = 0` forces zero bins). Time is
`Turing.TM2ComputableInPolyTime` on the fixed binary encoders `encInstance`, `encPolys`, `encTOut`, `encTBins`. -/
theorem theorem_1_3 :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ fk : Instance → TOut, ∃ fb : List (List (ℚ × ℚ)) → TBins,
        Nonempty (Turing.TM2ComputableInPolyTime encInstance encTOut fk) ∧
        Nonempty (Turing.TM2ComputableInPolyTime encPolys encTBins fb) ∧
        (∀ I : Instance, (∀ P ∈ I, 0 ≤ P.2) →
          (fk I).Sound I (box (1 + ε)) ∧
            ∀ S' : Finset (Fin I.n), TFeasible I S' →
              profit I S' ≤ C * (1 + Real.log (1 / ε)) * profit I ((fk I).indexSet I)) ∧
        (∀ l : List (List (ℚ × ℚ)), (∀ v ∈ l, FitsT v) →
          (fb l).Sound (Instance.ofPolys l) (box (1 + ε)) ∧
            ∀ (K : ℕ) (g : Fin (Instance.ofPolys l).n → Fin K),
              (∀ k : Fin K, TFeasible (Instance.ofPolys l) (Finset.univ.filter (fun i => g i = k))) →
                ((fb l).length : ℝ) ≤ C * (1 + Real.log (1 / ε)) * K) := by sorry

end PolygonPack.Supplement
