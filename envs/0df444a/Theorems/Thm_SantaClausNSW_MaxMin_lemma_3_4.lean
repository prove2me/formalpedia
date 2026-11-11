-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_4
-- name    : SantaClausNSW.MaxMin.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:09.45309+00:00
-- url     : https://prove2.me/theorems/f094bcb1-4c70-4740-8216-71537c604fb3
-- title:
--   Lemma 3.4 — a configuration solution with T > T_LP/6 in polynomial time (value queries for submodular, demand queries for subadditive)
-- statement:
--   There is a polynomial-time algorithm that either detects that $T_{LP}=0$ — in which case every allocation is optimal — or computes an explicit configuration solution with objective value $T$, supported on polynomially many configurations, with
--   $$T>\frac{T_{LP}}{6}.$$
--   For submodular valuations it uses only value queries; for subadditive valuations it uses only ordinary demand queries. With Theorem 3.5 and the supporting clauses of §3.4 it gives parts (i) and (ii) of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: running time polynomial in the encoding of the valuation values (§2, p. 10) → valuation values are a/b with naturals a, b ≤ 2^σ, b ≠ 0, and σ is part of the input (size n + m + σ); reason: App. E.1 (p. 67) makes the §2 convention concrete with the known bound σ
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: oracle queries with ties broken arbitrarily → an oracle is any fixed answer function correct on every well-formed question, quantified universally outside the probability over the coins; reason: the standard reading of 'ties broken arbitrarily'; malformed questions are unconstrained, so the program cannot rely on them
--   - encoding: an explicit configuration solution supported on polynomially many configurations → an output list of at most c·(1 + n + m + σ)^d well-formed triples (i, y_{i,S}, 1_S) forming a configuration solution with objective value T; reason: the paper's explicit format (p. 11) with the same polynomial as the time bound
--   - encoding: one algorithm with two query modes → two programs, one run with a value oracle (submodular), one with a demand oracle (subadditive), sharing c and d; reason: each uses only its class's queries, as stated
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 17, Lemma 3.4

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.4** (p. 17). There are two programs and constants `c, d` such that, for valuations
with values `a/b`, `a, b ≤ 2^σ`, every run on input `n, m, σ` halts within `c (1 + n + m + σ)^d`
work and either reports `T_LP = 0` — and then `T_LP = 0` and every allocation is optimal — or
outputs an explicit configuration solution with objective value `T`, supported on at most that
many configurations, with `T > T_LP/6`. For submodular valuations the program uses only value
queries; for subadditive valuations the other program uses only ordinary demand queries. -/
theorem lemma_3_4 :
    ∃ (Psub Pdem : Program) (c d : ℕ), ∀ (n m σ : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i)) → BitBounded v σ →
        ((∀ i, IsSubmodular (v i)) → ∀ O : Oracle, IsValueOracle v O →
          HaltsWithin Psub O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d) ∧
          ∀ s ∈ (run Psub O (c * (1 + oracleSize n m σ) ^ d + 1)
              (initState (oracleInput n m σ))).support,
            SolOutcome v (1 / 6) (c * (1 + oracleSize n m σ) ^ d) (outList s.mem) ∧
            (solFlag (outList s.mem) = 0 → ∀ A Y : Fin n → Finset (Fin m),
              IsAllocation A → IsAllocation Y → mmValue v Y ≤ mmValue v A)) ∧
        ((∀ i, IsSubadditive (v i)) → ∀ O : Oracle, IsDemandOracle v O →
          HaltsWithin Pdem O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d) ∧
          ∀ s ∈ (run Pdem O (c * (1 + oracleSize n m σ) ^ d + 1)
              (initState (oracleInput n m σ))).support,
            SolOutcome v (1 / 6) (c * (1 + oracleSize n m σ) ^ d) (outList s.mem) ∧
            (solFlag (outList s.mem) = 0 → ∀ A Y : Fin n → Finset (Fin m),
              IsAllocation A → IsAllocation Y → mmValue v Y ≤ mmValue v A)) := by sorry

end SantaClausNSW.MaxMin
