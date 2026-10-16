-- Prove2me | Theorems.Thm_PersistClust_Count_t5_cluster_chop
-- name    : PersistClust.Count.t5_cluster_chop
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T11:53:25.371885+00:00
-- url     : https://prove2.me/theorems/219dba34-a439-4017-a32a-54ec4f94eb0e
-- title:
--   Cluster chop: the per-cluster cluster-assembly bound with a net-witness hypothesis (generic, level-free)
-- statement:
--   Let X and Q be arbitrary types. Fix a real eps >= 0, a birth map bth : X -> R, a finite set s of points, per-point fibers fib : X -> Set Q, and a windowed supply family supply : R -> R -> Set Q. Assume: (hwin) every birth-window count is at most the supply cardinality on the window; (hcone) each in-window point's fiber lies in the supply; (hnet) a PER-WINDOW net-witness hypothesis: whenever every probe t with c - eps <= t <= d + eps admits a set point born in [c, d] within eps of t, the supply on [c, d] is covered by the fibers of the in-window points; and (hdisj) fibers of points admitting a cut with birth gap more than 2*eps are disjoint. Then |s| <= |union of the fibers of s|. This weakens the full-span net of the companion cluster-assembly lemma to a clause that only needs eps-nets window by window: the proof chops the sorted birth-value set at the first adjacent gap exceeding 2*eps, so each cluster carries its own net witness, cross-cluster fibers are disjoint, and the counts add. This is the counting engine behind the Hall-type demand census in persistence-based clustering, applied with bth the birth coordinate, fib the close-copy fibers, and supply the eps-expanded demand windows. All cardinalities are encard of sets; the statement is purely order- and set-theoretic.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the per-cluster (chop) refinement of the generic cluster-assembly covering lemma, with the net hypothesis in per-window net-witness form. Transcribed GREEN (exit 0, sorry-free) from the working file; the private helper exists_clusterChop (chop-point existence for nonempty finite birth-value sets: the [c, d] prefix is an eps-net of the expanded window and the rest is more than 2*eps above d, by induction peeling the maximum) is inlined verbatim above the target. The proof is pure Mathlib (generic over the point and fiber types).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_cluster_chop {X Q : Type}
    (ε : ℝ) (hε : 0 ≤ ε) (bth : X → ℝ) (s : Set X) (hs : s.Finite)
    (fib : X → Set Q) (supply : ℝ → ℝ → Set Q)
    (hwin : ∀ L R : ℝ, L ≤ R → {x : X | L ≤ bth x ∧ bth x ≤ R}.encard ≤ (supply L R).encard)
    (hcone : ∀ (L R : ℝ), L ≤ R → ∀ x ∈ s, L ≤ bth x → bth x ≤ R → fib x ⊆ supply L R)
    (hnet : ∀ L R : ℝ, L ≤ R →
        (∀ t : ℝ, L - ε ≤ t → t ≤ R + ε →
          ∃ x ∈ s, L ≤ bth x ∧ bth x ≤ R ∧ |bth x - t| ≤ ε) →
        supply L R ⊆ ⋃ x ∈ {x ∈ s | L ≤ bth x ∧ bth x ≤ R}, fib x)
    (hdisj : ∀ x ∈ s, ∀ x' ∈ s, ∀ t : ℝ, bth x ≤ t → t + 2 * ε < bth x' → fib x ∩ fib x' = ∅) :
    s.encard ≤ (⋃ x ∈ s, fib x).encard
    := by sorry
