-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_supporting_clauses
-- name    : SantaClausNSW.MaxMin.supporting_clauses
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:13.560934+00:00
-- url     : https://prove2.me/theorems/3b6665f0-e233-4e24-b2c8-2b3b4bf4a2a9
-- title:
--   §3.4 — supporting clauses for additive and submodular valuations
-- statement:
--   A supporting clause for $(i,S)$ is a vector $w\ge0$ on $S$ with
--   $$w(Q)\le v_i(Q)\ (Q\subseteq S),\qquad w(S)=v_i(S).\tag{13}$$
--   (a) For additive valuations $v_i(Q)=\sum_{j\in Q}v_{ij}$, the coefficients $w_j=v_{ij}$ satisfy (13). (b) For a normalized monotone submodular valuation, ordering the items of $S$ and giving each item its marginal value relative to the preceding items (Dobzinski–Nisan–Schapira) yields nonnegative coefficients satisfying (13), and (c) they require $O(|S|)$ value queries. These clauses feed Theorem 3.5.
--
--   Differences from the source:
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: w_j = v_{ij} for v_i(Q) = Σ_{j∈Q} v_{ij} → w_j = v({j}) for an additive valuation v; reason: for an additive valuation v_{ij} = v_i({j}); same instances
--   - encoding: ordering the items in S → a duplicate-free list ord with S = its set of entries; reason: an ordering of S is exactly such a list
--   - reading: require O(|S|) value queries → a program that, with any correct value oracle, halts on input n, m, i, 1_S after at most c·(|S| + 1) value queries and outputs a vector satisfying (13) on S (no time claim); reason: the paragraph claims a query count only; |S| + 1 covers S = ∅
--   - encoding: oracle queries with ties broken arbitrarily → an oracle is any fixed answer function correct on every well-formed question, quantified universally outside the probability over the coins; reason: the standard reading of 'ties broken arbitrarily'; malformed questions are unconstrained, so the program cannot rely on them
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 19, §3.4 (Additive valuations; Submodular valuations), with (13) on p. 17

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-- **§3.4, supporting clauses** (p. 19). (a) For an additive valuation the coefficients
`w_j = v({j})` satisfy (13) on every set `S`. (b) For a normalized monotone submodular valuation
the marginal clause of Dobzinski–Nisan–Schapira along any ordering of `S` is nonnegative and
satisfies (13). (c) A supporting clause is computed with `O(|S|)` value queries: there are a
program and a constant `c` that, with any correct value oracle for normalized monotone submodular
valuations, halt on input `n, m, i, 1_S` after at most `c (|S| + 1)` value queries and output
coefficients satisfying (13) on `S`. -/
theorem supporting_clauses :
    (∀ (m : ℕ) (v : Finset (Fin m) → ℝ), IsValuation v → IsAdditive v →
      ∀ S : Finset (Fin m), IsSupportingClause v S (fun j => v {j})) ∧
    (∀ (m : ℕ) (v : Finset (Fin m) → ℝ), IsValuation v → IsSubmodular v →
      ∀ ord : List (Fin m), ord.Nodup →
        IsSupportingClause v ord.toFinset (marginalClause v ord)) ∧
    (∃ (P : Program) (c : ℕ), ∀ (n m : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
      (∀ i, IsValuation (v i) ∧ IsSubmodular (v i)) → ∀ O : Oracle, IsValueOracle v O →
      ∀ (i : Fin n) (S : Finset (Fin m)), ∃ K : ℕ,
        ∀ s ∈ (run P O K (initState ([(n : ℚ), (m : ℚ), ((i : ℕ) : ℚ)] ++ encSet S))).support,
          s.halted = true ∧ s.queries ≤ c * (S.card + 1) ∧
          IsSupportingClause (v i) S (fun j => ((outList s.mem).getD (j : ℕ) 0 : ℝ))) := by sorry

end SantaClausNSW.MaxMin
