-- Prove2me | Theorems.Thm_PolygonPack_lemma_E_1
-- name    : PolygonPack.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:38.78928+00:00
-- url     : https://prove2.me/theorems/5e8692fd-6b68-47c8-97f9-a6ce62de3ed8
-- title:
--   Lemma E.1 — packing a bounded number of polygons
-- statement:
--   For every fixed $k$ there is a polynomial-time machine which, on $k$ polygons of positive area with rational vertices and any number of vertices each, decides whether they can all be packed in the unit square under rotations and translations and, when they can, returns a packing as exact real algebraic numbers.
--
--   This is the exact geometric test behind the exceptional candidate.
--
--   Differences from the source:
--   - encoding: k polygons without profits → an instance with zero profits; reason: Feasible and Out.Sound then apply; profits play no role
--   - reading: polynomial time in the total binary encoding length → Nonempty (Turing.TM2ComputableInPolyTime …) on the fixed binary encoders; reason: p.13 names this measure; the paper fixes no machine model
--   - reading: placements returned as exact real algebraic numbers of polynomial description length → each pose number as a nonzero integer polynomial with a rational interval isolating its root; reason: the per-coordinate form of p.48; description length follows from the time bound
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma E.1, p.46

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

namespace PolygonPack

/-- **Lemma E.1 (Packing a bounded number of polygons).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.46. "For every fixed k, feasibility of k positive-area convex polygons in a unit square under rotations and translations can be decided in time
polynomial in the total binary input length. When feasible, a packing can be returned as exact real algebraic numbers of polynomial description length. The bound permits an arbitrary number of vertices in each
polygon."

One machine for each `k`. On `k` positive-area polygons, the answer is `none` exactly when they cannot all be packed, and otherwise an output that denotes a packing of all of them.

**Formalization Note.** The bound is on the number of polygons only: a vertex list has any length. The per-coordinate `AlgNum` form replaces the configuration-wide real univariate representation of p.46 (see
`AlgNum`). The polygons are read as an instance with zero profits, so `Feasible`, `Out.Sound` apply. -/
theorem lemma_E_1 (k : ℕ) :
    ∃ f : List (List (ℚ × ℚ)) → Option Out, Nonempty (Turing.TM2ComputableInPolyTime encPolys encOptOut f) ∧
      ∀ polys : List (List (ℚ × ℚ)), polys.length = k → (∀ v ∈ polys, PosArea v) →
        (f polys = none ↔ ¬ Feasible (Instance.ofPolys polys) Finset.univ) ∧
        ∀ out : Out, f polys = some out →
          out.Sound (Instance.ofPolys polys) ∧ out.indexSet (Instance.ofPolys polys) = Finset.univ := by sorry

end PolygonPack
