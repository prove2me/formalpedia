-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_theorem_3_12
-- name    : SantaClausNSW.MaxMin.theorem_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:19.145201+00:00
-- url     : https://prove2.me/theorems/a9ce5cee-cfdd-4973-a1fa-4f0414ee547e
-- title:
--   Theorem 3.12 — subadditive valuations, any number of items: O(√n)-approximation with demand queries, single run ≥ 3/4, repetitions ≥ 1 − 4^{−q}
-- statement:
--   For normalized monotone subadditive valuations and any number of items there is a randomized polynomial-time $O(\sqrt n)$-approximation algorithm for max-min allocation using ordinary demand queries: there is a constant $C>0$ such that a single run outputs an allocation $A$ with
--   $$\mathrm{OPT}_{MM}\le C\sqrt n\cdot\min_i v_i(A_i)$$
--   with probability at least $3/4$, and independent repetitions make the failure probability arbitrarily small — after $q$ runs, keeping the allocation with the largest minimum value, it is at most $4^{-q}$. It is part (iii) of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: running time polynomial in the encoding of the valuation values (§2, p. 10) → valuation values are a/b with naturals a, b ≤ 2^σ, b ≠ 0, and σ is part of the input (size n + m + σ); reason: App. E.1 (p. 67) makes the §2 convention concrete with the known bound σ
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: oracle queries with ties broken arbitrarily → an oracle is any fixed answer function correct on every well-formed question, quantified universally outside the probability over the coins; reason: the standard reading of 'ties broken arbitrarily'; malformed questions are unconstrained, so the program cannot rely on them
--   - encoding: the returned allocation → the first m entries of the output list: entry j = i + 1 gives item j to agent i, any other value leaves j unassigned; reason: every output decodes to an allocation; nothing is excluded
--   - encoding: OPT_MM ≤ O(√n) · min_i v_i(A_i) → ∃ C > 0 fixed before the input with min_i v_i(Y_i) ≤ C√n · min_i v_i(A_i) for every allocation Y; reason: OPT_MM is the maximum of min_i v_i(Y_i) over allocations; same claim
--   - reading: 'independent repetitions can make the failure probability arbitrarily small' → a coin-only program taking q ≥ 1 that halts within c·(1 + n + m + σ + q)^d work and succeeds with probability ≥ 1 − (1/4)^q, with the same C; reason: the proof (p. 33): 'After q runs, the probability that all runs fail is at most 4^{−q}'; the uniform-in-q reading is the stronger one
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 32, Theorem 3.12 (repetition bound in its proof, p. 33)

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-- **Theorem 3.12** (p. 32). For normalized monotone subadditive valuations (values `a/b`,
`a, b ≤ 2^σ`) and any number of items, there are a constant `C > 0`, fair-coin programs and
constants `c, d` such that, with any correct ordinary demand oracle: a single run halts within
`c (1 + n + m + σ)^d` work and with probability at least `3/4` outputs an allocation `A` with
`min_i v_i(Y_i) ≤ C √n · min_i v_i(A_i)` for every allocation `Y`; and `q ≥ 1` independent
repetitions (keeping the best allocation) halt within `c (1 + n + m + σ + q)^d` work and succeed
with probability at least `1 − 4^{−q}`. -/
theorem theorem_3_12 :
    ∃ C : ℝ, 0 < C ∧ ∃ (P Prep : Program) (c d : ℕ), CoinOnly P ∧ CoinOnly Prep ∧
      ∀ (n m σ : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i) ∧ IsSubadditive (v i)) →
      BitBounded v σ → ∀ O : Oracle, IsDemandOracle v O →
        (HaltsWithin P O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d) ∧
          outProb P O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d)
            (fun l => MMApprox v (C * Real.sqrt n) (decAlloc n m l)) ≥ 3 / 4) ∧
        ∀ q : ℕ, 1 ≤ q →
          HaltsWithin Prep O (oracleInput n m σ ++ [(q : ℚ)])
            (c * (1 + oracleSize n m σ + q) ^ d) ∧
          outProb Prep O (oracleInput n m σ ++ [(q : ℚ)]) (c * (1 + oracleSize n m σ + q) ^ d)
            (fun l => MMApprox v (C * Real.sqrt n) (decAlloc n m l)) ≥ 1 - (1 / 4 : ℝ) ^ q := by sorry

end SantaClausNSW.MaxMin
