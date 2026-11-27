-- Prove2me | Theorems.Thm_SingleExpBisect_Main_shrink_to_terminals_time
-- name    : SingleExpBisect.Main.shrink_to_terminals_time
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:49:52.76564+00:00
-- url     : https://prove2.me/theorems/36fe7b49-d6a0-41d2-b69c-2250f23f89ad
-- title:
--   Lemma 5.1: a time-bounded TM2 for shrinking to an admissible terminal set
-- statement:
--   One fixed deterministic Boolean multistack Turing machine reads the registered graph, parameter and two vertex sets X ⊆ B. If X = B it outputs the unbreakable-bag flag. Otherwise it outputs X in the registered shrink format. It halts within 64·2^(64k)·(n+1)^64 steps. Whenever |X| ≤ 2k+1, the output meets the alternatives of Lemma 5.1 provided that X = B, |X| ≤ 2k, or every component outside X has at most 2k neighbours in X. In particular it covers all graphs and bags when |X| ≤ 2k, without a promise on the adhesion of B.
-- source:
--   S. Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, Section 5, Lemma 5.1. Implementation for the admissible-terminal branch of Prove2Me STOC project 803.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Encodings
import Definitions.Def_SingleExpBisect_Main_Graphs

open scoped Classical
open SingleExpBisect.Main MinBisectFPT

theorem SingleExpBisect.Main.shrink_to_terminals_time :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n)),
      X ⊆ B → let out := if X=B then [false] else true::encodeSet X
      HMBinPacking.OutputsWithin M (encodeInput H k ++ encodeSet X ++ encodeSet B) out (stepBound 64 k n) ∧
      (X.card ≤ 2*k+1 → (X=B ∨ X.card ≤ 2*k ∨ adh H X ≤ 2*k) →
        ((out=[false] ∧ IsEdgeUnbreakable H Finset.univ B (2*k) k) ∨
          ∃ B' : Finset (Fin n), out=true::encodeSet B' ∧ X ⊆ B' ∧ B'.card < B.card ∧ adh H B' ≤ 2*k)) := by sorry
