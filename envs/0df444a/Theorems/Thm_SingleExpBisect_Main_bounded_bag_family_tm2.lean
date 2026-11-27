-- Prove2me | Theorems.Thm_SingleExpBisect_Main_bounded_bag_family_tm2
-- name    : SingleExpBisect.Main.bounded_bag_family_tm2
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:28:09.325545+00:00
-- url     : https://prove2.me/theorems/584df4be-8e48-4010-9fa8-654dc07151ed
-- title:
--   Lemma 3.11: a single time-bounded TM2 for exact bounded-size powerset enumeration; full guarantees on bags of size O(k+log n)
-- statement:
--   For every input graph, parameter, and bag B, one fixed finite deterministic multi-stack TM2 produces all subsets of B of cardinality at most 2k, in the registered binary encodings, in at most 65536·4^|B|·(n+k+1)^4 actual machine steps. The same machine satisfies all mathematical output conditions and the parameterized running time of Lemma 3.11 whenever 2^|B| ≤ 2^(qk)·(n+1)^q for a fixed q, equivalently |B| ≤ q(k+log₂(n+1)).
-- source:
--   S. Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, Lemma 3.11 (project 803).

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Encodings
import Definitions.Def_SingleExpBisect_Main_Graphs

open scoped Classical
open SingleExpBisect.Main MinBisectFPT

theorem SingleExpBisect.Main.bounded_bag_family_tm2 :
    ∃ M : Turing.TM2ComputableAux Bool Bool,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L)
            (65536 * 4^B.card * (n+k+1)^4) ∧
          (∀ D : Finset (Fin n), D ∈ L ↔ D ⊆ B ∧ D.card ≤ 2*k) ∧ L.length ≤ 2^B.card) ∧
      ∀ q : ℕ, ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        2^B.card ≤ 2^(q*k)*(n+1)^q →
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L) (stepBound C k n) ∧
          (∀ D ∈ L, D ⊆ B ∧ D.card ≤ 2*k) ∧
          (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧ L.toFinset.card ≤ stepBound C k n ∧
          ∀ A : Finset (Fin n), (A = ∅ ∨ (G.induce (A : Set _)).Connected) →
            cutSize G A ≤ k → (A ∩ B).card ≤ 2*k → A ∩ B ∈ L := by sorry
