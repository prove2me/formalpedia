-- Prove2me | Theorems.Thm_PolygonPack_Supplement_theorem_1_2
-- name    : PolygonPack.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:15:06.507111+00:00
-- url     : https://prove2.me/theorems/17a0a7d9-0cea-4752-918b-a87c38e27829
-- title:
--   Theorem 1.2 — absolute 17-approximation for bin packing of convex polygons under rotations
-- statement:
--   There is a function $f$, computed by a deterministic Turing machine in time polynomial in the binary length of its input, with the following property. Let $P_0,\dots,P_{n-1}$ be convex polygons with rational vertices, each of positive area and each fitting alone in the unit square under some rotation and translation. Then $f$ returns a list of $N$ bins with exact algebraic rotations and translations that packs every polygon exactly once into unit squares (pairwise disjoint interiors within each bin), and
--   $$N\le 17K$$
--   for every $K\in\mathbb N$ such that the polygons can be distributed over $K$ unit squares, each of which they fit in under rotations and translations.
--
--   This is the paper's bin-packing theorem: an **absolute** 17-approximation, with no additive term, for packing convex polygons under arbitrary rotations into the minimum number of unit squares. It complements the knapsack result, Theorem 1.1.
--
--   Differences from the source:
--   - reading: deterministic polynomial-time algorithm → one function f with Nonempty (Turing.TM2ComputableInPolyTime encPolys encBins f); reason: p.13 measures time in the total binary encoding length; a machine computing a function is deterministic; as in the published Theorem 1.1
--   - reading: the packing the algorithm returns → a list of bins, each a base Out with exact algebraic poses that is Out.Sound, the concatenated indices a permutation of 0..n−1; reason: p.74 "Both algorithms retain exact descriptions of their computed placements"; every polygon must be packed (p.4)
--   - reading: convex polygons, each individually fitting into a unit square → polygons of positive area that each fit alone in the unit square under a rigid pose (base Instance.Valid of Instance.ofPolys l); reason: App. E, p.46: "We assume that polygons have positive area", the setting of the exact placements the algorithm uses; same convention as the published Theorem 1.1
--   - generalization: convex polygons given by their rational vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
--   - encoding: the minimum number K of unit squares → the bound length ≤ 17·K for every K and every assignment of the polygons to K squares whose parts are feasible; reason: equivalent to a bound by the optimum; K = 0 covers the empty instance, which requires zero bins (p.74)
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.2, p.73 (PDF p.74); informal form p.2 (PDF p.3); proof pp.73–74

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_AlgNum
import Definitions.Def_PolygonPack_Out
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_encOut
import Definitions.Def_PolygonPack_Supplement_Bins

namespace PolygonPack.Supplement

open PolygonPack

/-- **Theorem 1.2.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), Theorem 1.2, p.73 (PDF p.74); informal form p.2 (PDF p.3); proof pp.73–74. "There is a deterministic polynomial-time absolute 17-approximation algorithm for packing convex polygons, each individually fitting into a unit square, into the minimum number of unit squares, allowing arbitrary rotations and translations."

There is one function `f`, computed by a polynomial-time Turing machine from binary polygon lists to lists of
bins with exact algebraic poses, such that on every list of positive-area polygons each fitting alone in the
unit square, the output packs every polygon exactly once into unit squares, and it uses at most `17·K` bins
whenever the polygons can be distributed over `K` unit squares.

**Formalization Note.** "Polynomial time" is `Turing.TM2ComputableInPolyTime` on the fixed binary encoders
`encPolys`, `encBins`, as for Theorem 1.1. "Absolute" means no additive term: the bound `17·K` holds for every
`K`, with `K = 0` forcing zero bins on the empty list. The optimum is not named: the comparator is every
assignment `g` of the polygons to `K` squares whose every part is feasible under rotations and translations.
Positive area is the base `Instance.Valid` (App. E, p.46); profits are zero (`Instance.ofPolys`). -/
theorem theorem_1_2 :
    ∃ f : List (List (ℚ × ℚ)) → Bins, Nonempty (Turing.TM2ComputableInPolyTime encPolys encBins f) ∧
      ∀ l : List (List (ℚ × ℚ)), (Instance.ofPolys l).Valid →
        (f l).Sound (Instance.ofPolys l) ∧
          ∀ (K : ℕ) (g : Fin (Instance.ofPolys l).n → Fin K),
            (∀ k : Fin K, Feasible (Instance.ofPolys l) (Finset.univ.filter (fun i => g i = k))) →
              (f l).length ≤ 17 * K := by sorry

end PolygonPack.Supplement
