-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_2_7_combining_contractions
-- name    : SubexpPrimes.lemma_2_7_combining_contractions
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:14.662333+00:00
-- url     : https://prove2.me/theorems/b651e416-94c5-4601-a8b0-3ca818d1cf32
-- title:
--   Lemma 2.7 — combining contractions
-- statement:
--   Let $s\ge2$ and $0\le\rho=O(s)$. Let $G_1,\dots,G_h$ be networks of description length at most $L$, with $h\le\mathrm{poly}(s)$, each satisfying the hypotheses of Theorem 2.5 with $\Theta(s)$ edges and $O(s)$ weighted vertices of precision $O(s)$. Let $b_1,\dots,b_h$ and $a_1,\dots,a_h$ be integers with $|b_j|\le2^{O(s)}$ and $|a_j|=O(s)$. Then
--
--   $$
--   S=\sum_{j=1}^h b_j2^{a_j}Z(G_j)
--   $$
--
--   can be computed to within $2^{-\rho}$ in time $\mathrm{poly}(s+L)\,2^{O(s/\sqrt{\log s})}$ and polynomial space.
--
--   Differences from the source:
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace, which counts every tape including the input; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat, and any reasonable model states the same class of bound
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: E(cs) for a constant c → the constant absorbed into K; reason: E(cx) and E(x) are the same class for x ≥ 2
--   - encoding: Θ(s) edges → s ≤ c m_j and m_j ≤ c s; reason: Θ is two-sided; the weighted vertices and the precision are O(s) through Evaluable
--   - encoding: the output, computed to within 2^{−ρ} → a dyadic number, as an integer and an exponent; reason: the proof outputs a sum of dyadic numbers
--   - encoding: each network satisfies the hypotheses of Theorem 2.5, with entry algorithms in time poly(m + L) → the entry machine E runs within time and space c(m + L + 1)^c; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma 2.7, p.16

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_CombTerm

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Lemma 2.7 (Combining contractions)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.16.

Let `s ≥ 2` and `0 ≤ ρ = O(s)`. Let `G₁, …, G_h` be networks of description length at most `L`, with
`h ≤ poly(s)`, each satisfying the hypotheses of Theorem 2.5 with `Θ(s)` edges and `O(s)` weighted
vertices of precision `O(s)`, and `b_j`, `a_j` integers with `|b_j| ≤ 2^{O(s)}`, `|a_j| = O(s)`. Then
`S = ∑_j b_j 2^{a_j} Z(G_j)` can be computed to within `2^{-ρ}` in time `poly(s + L) E(cs)` and
polynomial space.

**Formalization Note.** `∀ c, E, T ∃ A K ∀` instances. "`Θ(s)`" is two-sided: `s ≤ c m_j` and
`m_j ≤ c s`. The paper's `c` in `E(cs)` is absorbed into `K`. An empty list is allowed, with `S = 0`.
The output is a dyadic number. -/
theorem lemma_2_7_combining_contractions :
    ∀ (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
    ∃ (A : PrimitiveMachine) (outA : Fin A.tapeCount) (K : ℕ),
    ∀ (T : (D : NetDesc) → D.Tables ℚ) (s ρ L : ℕ) (ts : List CombTerm),
      2 ≤ s → ρ ≤ c * s → ts.length ≤ c * s ^ c →
      (∀ t ∈ ts, TermOK c s E outE T t ∧ t.D.encode.length ≤ L) →
      ∃ (k : ℤ) (j : ℕ),
        |(k : ℝ) / 2 ^ j - combValue T ts| ≤ (2 : ℝ) ^ (-(ρ : ℤ)) ∧
        RunsWithin A outA
          (Encoding.encodeList id [Encoding.encodeNat ρ, combWord ts])
          (dyadicWord k j)
          (subexpBound K (s + L) s)
          (polyBound K (s + L)) := by sorry

end SubexpPrimes
