-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_agreement_lemma_majority
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.agreement_lemma_majority
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:45:52.786291+00:00
-- url     : https://prove2.me/theorems/4e3b64b6-1c3f-49df-83aa-775cb0fcb41d
-- title:
--   Lemma 16 — agreement lemma for majority
-- statement:
--   Write $p=\lceil n/2\rceil-1$. There are an absolute constant $c_0>0$ and a threshold $N\ge1$ such that the following holds for every $n\ge N$. Let $\Sigma$ be a finite alphabet with $|\Sigma|\le c_0\sqrt n$, and suppose that for every $S\subseteq[n]$ with $|S|\ge p+1$ we are given a coloring $\alpha_S:S\to\Sigma$. Then there are sets $T,S\subseteq[n]$ with $|T|\ge p+1$ and $|S|\ge p+1$ such that
--
--   1. $T\subsetneq S$, and
--   2. $\alpha_T$ and $\alpha_S|_T$ disagree on at most $p$ points:
--
--   $$\#\{i\in T:\alpha_T(i)\ne\alpha_S(i)\}\le p.$$
--
--   Both sets are nonempty, since $p+1\ge1$. The lemma is the combinatorial core of the alphabet lower bound for majority (Theorem 22).
--
--   **Formalization Note** $p+1=\lceil n/2\rceil$ is written `(n + 1) / 2 - 1 + 1` in natural numbers, which equals $\lceil n/2\rceil$ for $n\ge1$. The family takes the set together with the proof of its size bound.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: an arbitrary finite alphabet Σ → a finite type Sig in an arbitrary universe; reason: every finite set is in bijection with a finite type; only |Σ| enters the statement
--   - encoding: for sufficiently large n and a sufficiently small absolute constant c0 > 0 → ∃ c0 > 0, ∃ N ≥ 1, ∀ n ≥ N; reason: this is the meaning of the two existential constants; c0 and N do not depend on Σ or the family
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 13, Lemma 16 (proof pp. 13–14)

import Mathlib

namespace SymmetricPSM1041.ORLowerBound.Supplement

open Classical in
theorem agreement_lemma_majority :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (Sig : Type*) [Fintype Sig], (Fintype.card Sig : ℝ) ≤ c₀ * Real.sqrt n →
      ∀ α : (S : Finset (Fin n)) → (n + 1) / 2 - 1 + 1 ≤ S.card → (i : Fin n) → i ∈ S → Sig,
      ∃ (T S : Finset (Fin n)) (hT : (n + 1) / 2 - 1 + 1 ≤ T.card)
        (hS : (n + 1) / 2 - 1 + 1 ≤ S.card), T ⊂ S ∧
        (Finset.univ.filter (fun i : Fin n => ∃ (hiT : i ∈ T) (hiS : i ∈ S),
            α T hT i hiT ≠ α S hS i hiS)).card ≤ (n + 1) / 2 - 1 := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
