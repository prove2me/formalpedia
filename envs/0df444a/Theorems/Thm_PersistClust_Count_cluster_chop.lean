-- Prove2me | Theorems.Thm_PersistClust_Count_cluster_chop
-- name    : PersistClust.Count.cluster_chop
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T06:46:59.845985+00:00
-- url     : https://prove2.me/theorems/08f85f75-9bd3-4614-8fc0-e676f0d0dcac
-- title:
--   Generic cluster chop: Hall-style fiber count by chopping the birth set at the first wide gap
-- statement:
--   Let X and Q be types, ε a nonnegative real (hε : 0 ≤ ε), bth : X → ℝ a birth function, s : Set X a finite set of demands (hs : s.Finite), fib : X → Set Q a fiber assignment for each demand, and supply : ℝ → ℝ → Set Q a family of supply sets indexed by the two ends of a real window. Assume the window inequality hwin: for every L ≤ R, the set of all points of X whose birth lies in the closed window [L, R] has at most as many elements (encard) as supply L R. Assume the cone inclusions hcone: for every L ≤ R, each demand x ∈ s with birth in [L, R] has fib x ⊆ supply L R. Assume the net cover hnet in its net-witness form: for every L ≤ R, whenever every point t of the ε-expanded window [L − ε, R + ε] lies within ε of the birth of some demand x ∈ s with L ≤ bth x ≤ R, then supply L R is contained in the union of the fibers of the s-demands whose birth lies in [L, R]. Assume the 2ε-separation hdisj: whenever two demands x, x' ∈ s admit a level t with bth x ≤ t and t + 2ε < bth x', their fibers are disjoint. Then the demand set counts into its fiber union: s.encard ≤ (⋃ x ∈ s, fib x).encard. Proof: unlike the full-window assembly (which needs the one-shot net property — false for sparse s), the finite set of distinct births of a threshold slice T = {x ∈ s | u < bth x} is chopped (by an induction on Finset cardinality that erases the maximal birth) at a first cluster [c, d] whose births ε-net the expanded window [c − ε, d + ε] and whose first gap wider than 2ε sits right after d; the count of the lower part {x ∈ T | bth x ≤ d} comes from the window inequality hwin at [c, d] plus the net cover hnet applied to the cluster's net witnesses; the fiber unions of the two parts are disjoint by hdisj and the gap property; the upper part {x ∈ T | d < bth x} equals {x ∈ s | d + 2ε < bth x} and has strictly fewer demands, so it goes through the induction on the slice cardinality; the counts recombine additively by the disjointness, and finally s itself is the threshold slice above bth m − 1 for a birth-minimal demand m.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the internal-cluster-chop generalization of the published PersistClust.Count.cluster_assembly backbone (t5_cluster_chop in the rankKill master, Scratch_rankR1 L7749-7915, with its private helper exists_clusterChop at L7655-7737) — consumed by the sparse-slice sites of the T5 matching-census assembly: a finite demand set with real birth values counts into its fiber union by chopping the birth Finset at the first > 2ε adjacent gap and running the window inequality plus the per-cluster net cover, with the remainder handled by induction on the slice cardinality.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem cluster_chop {X Q : Type}
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
