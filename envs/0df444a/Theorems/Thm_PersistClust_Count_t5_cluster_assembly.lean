-- Prove2me | Theorems.Thm_PersistClust_Count_t5_cluster_assembly
-- name    : PersistClust.Count.t5_cluster_assembly
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T11:44:54.002182+00:00
-- url     : https://prove2.me/theorems/22e212b5-8612-46c5-9d25-7585f61ade43
-- title:
--   Cluster assembly: a windowed fiber-count bound for finite birth-point sets (generic, level-free)
-- statement:
--   Let X and Q be arbitrary types. Fix a real eps >= 0, a birth map bth : X -> R, a finite set s of points, a per-point fiber family fib : X -> Set Q, and a two-parameter windowed supply family supply : R -> R -> Set Q. Assume: (hwin) for every window [L, R], the number of s-points with birth inside the window is at most the cardinality of supply(L, R); (hcone) for every window and every point of s born inside it, the point's fiber lies inside supply(L, R); (hnet) for the full span window whose bounds cover all births of s, the supply is covered by the union of the fibers of s; and (hdisj) whenever two points of s admit a cut level t with bth(x) <= t and t + 2*eps < bth(x'), their fibers are disjoint. Then the cardinality of s is at most the cardinality of the union of all fibers: |s| <= |U_{x in s} fib(x)|. This is a generic combinatorial covering lemma: window counts bound the set through the supply, cones place fibers inside supplies, the net covers the supply by fibers, and the disjointness clause separates fibers across birth gaps; it is the counting skeleton behind Hall-type matching arguments in persistence-based clustering, applied there with bth the birth coordinate, fib the close-copy equivalence classes, and supply the eps-expanded windows of the demand census. All cardinalities are encard of sets; the statement is purely order- and set-theoretic.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the generic cluster-assembly covering lemma (window count bound + fiber cones + supply net + gap-disjointness give the fiber-union bound). Transcribed GREEN (exit 0, sorry-free) from the working file; the proof is pure Mathlib (generic over the point and fiber types), no platform-Definition dependencies and no in-file helper closure needed.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_cluster_assembly {X Q : Type}
    (ε : ℝ) (hε : 0 ≤ ε) (bth : X → ℝ) (s : Set X) (hs : s.Finite)
    (fib : X → Set Q) (supply : ℝ → ℝ → Set Q)
    (hwin : ∀ L R : ℝ, L ≤ R → {x : X | L ≤ bth x ∧ bth x ≤ R}.encard ≤ (supply L R).encard)
    (hcone : ∀ (L R : ℝ), L ≤ R → ∀ x ∈ s, L ≤ bth x → bth x ≤ R → fib x ⊆ supply L R)
    (hnet : ∀ (L R : ℝ), L ≤ R → (∀ x ∈ s, L ≤ bth x → bth x ≤ R) → supply L R ⊆ ⋃ x ∈ s, fib x)
    (hdisj : ∀ x ∈ s, ∀ x' ∈ s, ∀ t : ℝ, bth x ≤ t → t + 2 * ε < bth x' → fib x ∩ fib x' = ∅) :
    s.encard ≤ (⋃ x ∈ s, fib x).encard
    := by sorry
