-- Prove2me | Theorems.Thm_SparseDisc_lemma_8_26
-- name    : SparseDisc.lemma_8_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:55:38.259031+00:00
-- url     : https://prove2.me/theorems/478c375b-746a-4b25-8d7e-2172c01bc519
-- title:
--   Lemma 8.26 — near-cover lemma
-- statement:
--   Let $S \ne \emptyset$ be finite.
--
--   1. If $U \cup V = \{\pm1\}^S$, then $U$ or $V$ contains a near-loop.
--   2. Consequently any two near-thick subsets of $\{\pm1\}^S$ intersect.
--
--   This is the near-loop analogue of the separation lemma (Theorem 1.11(a)), with intersection in place of distance at most 1.
--
--   Differences from the source: none.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 8.26, p.41

import Mathlib
import Definitions.Def_SparseDisc_IsNearThick

namespace SparseDisc

/-- **Lemma 8.26 (near-cover lemma)** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.41). Let `S ≠ ∅` and
`U ∪ V = {±1}^S`. Then `U` or `V` contains a near-loop. Consequently any two near-thick subsets of
`{±1}^S` intersect. -/
theorem lemma_8_26 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] :
    (∀ A B : Set (Cube S), A ∪ B = Set.univ → HasNearLoop A ∨ HasNearLoop B) ∧
    (∀ Ω₁ Ω₂ : Set (Cube S), IsNearThick Ω₁ → IsNearThick Ω₂ → (Ω₁ ∩ Ω₂).Nonempty) := by sorry

end SparseDisc
