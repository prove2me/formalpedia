-- Prove2me | Theorems.Thm_PersistClust_Count_cluster_assembly
-- name    : PersistClust.Count.cluster_assembly
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T05:05:36.481041+00:00
-- url     : https://prove2.me/theorems/28284203-045e-4936-9f7f-85a57799e817
-- title:
--   Generic Hall-style cluster assembly: a finite demand set counts into its fiber union
-- statement:
--   Let X and Q be types, with a finite set s of demands in X, a real birth value bth x for each demand, a fiber fib x (a subset of Q) for each demand, a two-parameter family of supply sets supply L R (subsets of Q) indexed by real window ends, and a nonnegative ε (hε : 0 ≤ ε). Assume the window inequality hwin: for every closed window [L, R], the set of demands whose birth lies in the window has at most as many elements as the supply for that window; the cone inclusions hcone: inside a window [L, R], each demand in s with birth in the window has its fiber contained in the window's supply; the net cover hnet: whenever every demand in s has birth in the window [L, R], the window's supply is contained in the union of all demand fibers; and the 2ε-separation hdisj: whenever two demands x, x' in s have births separated through an intermediate level t (bth x ≤ t and t + 2ε < bth x'), their fibers are disjoint. Then the demand set counts into its fiber union: s.encard ≤ (⋃ x ∈ s, fib x).encard. Proof: take the full window [bth m, bth M] spanned by a birth-minimal element m and a birth-maximal element M of s; every demand lies in this window by minimality/maximality, so the window inequality bounds the demand count by the window supply's count, and the net cover applies there (its side condition — every member's birth stays at or below the window top — is witnessed by the maximal birth itself), turning the supply into a subset of the fiber union; two encard monotonicity steps chain the containments into the count. (The cone inclusions and the separation hypothesis record the cluster geometry for downstream use; the count itself needs only the window inequality and the net cover.)
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the generic Hall-style cluster-assembly backbone consumed by the hqcB site of the T5 matching-census assembly (t5_cluster_assembly in the rankKill master, Scratch_rankR1 L7615-L7645) — a finite demand set with real birth values counts into its fiber union by applying the window inequality and the net cover once at the full window spanned by the minimal and maximal birth values.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem cluster_assembly {X Q : Type}
    (ε : ℝ) (hε : 0 ≤ ε) (bth : X → ℝ) (s : Set X) (hs : s.Finite)
    (fib : X → Set Q) (supply : ℝ → ℝ → Set Q)
    (hwin : ∀ L R : ℝ, L ≤ R → {x : X | L ≤ bth x ∧ bth x ≤ R}.encard ≤ (supply L R).encard)
    (hcone : ∀ (L R : ℝ), L ≤ R → ∀ x ∈ s, L ≤ bth x → bth x ≤ R → fib x ⊆ supply L R)
    (hnet : ∀ (L R : ℝ), L ≤ R → (∀ x ∈ s, L ≤ bth x → bth x ≤ R) → supply L R ⊆ ⋃ x ∈ s, fib x)
    (hdisj : ∀ x ∈ s, ∀ x' ∈ s, ∀ t : ℝ, bth x ≤ t → t + 2 * ε < bth x' → fib x ∩ fib x' = ∅) :
    s.encard ≤ (⋃ x ∈ s, fib x).encard
    := by sorry
