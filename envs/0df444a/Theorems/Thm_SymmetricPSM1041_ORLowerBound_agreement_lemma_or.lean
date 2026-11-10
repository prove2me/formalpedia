-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_agreement_lemma_or
-- name    : SymmetricPSM1041.ORLowerBound.agreement_lemma_or
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:14.038963+00:00
-- url     : https://prove2.me/theorems/4155eb0c-7335-4a4b-b71f-04a908882cd2
-- title:
--   Lemma 13 — agreement on nested nonempty subsets
-- statement:
--   For each alphabet cardinality $k\ge0$ there is a positive threshold $N$ such that the following holds for every finite alphabet $\Sigma$ of cardinality $k$ and every $n\ge N$. Given a function $\alpha_S:S\to\Sigma$ for each nonempty subset $S\subseteq[n]$, there exist nonempty sets $T\subsetneq S$ with
--
--   $$\forall i\in T:\ \alpha_T(i)=\alpha_S(i).$$
--
--   The threshold depends only on the cardinality, not on the labels, on $n$ or on the family. The smaller set is required to be nonempty, and the containment is strict. This is the agreement obstruction used in the OR alphabet lower bound.
--
--   Differences from the source:
--   - encoding: nonempty subsets of [n] and functions on each subset → nonempty Finsets of Fin n with membership-indexed functions; reason: every subset of Fin n is finite; proof arguments do not change functions on its elements
--   - encoding: N(Σ) depending only on |Σ| → k precedes the existential threshold, followed by every alphabet of cardinality k; reason: this makes the source’s cardinality-uniform quantifier order explicit
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 12, Lemma 13 (proof continues p. 13)

import Mathlib

namespace SymmetricPSM1041.ORLowerBound

theorem agreement_lemma_or (k : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (Alphabet : Type*) [Fintype Alphabet], Fintype.card Alphabet = k →
      ∀ n : ℕ, N ≤ n →
      ∀ α : (S : Finset (Fin n)) → S.Nonempty → (i : Fin n) → i ∈ S → Alphabet,
      ∃ T S : Finset (Fin n), ∃ hT : T.Nonempty, ∃ hS : S.Nonempty,
        ∃ hTS : T ⊂ S, ∀ (i : Fin n) (hi : i ∈ T),
          α T hT i hi = α S hS i ((le_of_lt hTS) hi) := by sorry

end SymmetricPSM1041.ORLowerBound
