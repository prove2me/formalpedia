-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_theorem_1_1
-- name    : SantaClausNSW.MaxMin.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:11.282931+00:00
-- url     : https://prove2.me/theorems/d6acfad6-fa26-452a-ae0e-7e10a10bad8a
-- title:
--   Theorem 1.1 — randomized polynomial-time O(√n)-approximation for max-min allocation: additive, submodular (value queries), subadditive (demand queries)
-- statement:
--   In **max-min allocation** (the Santa Claus problem) $n\ge1$ agents with valuations $v_i$ share $m$ indivisible items, and the goal is an allocation $A$ maximizing $\min_iv_i(A_i)$; $\mathrm{OPT}_{MM}$ is the optimum. The theorem gives randomized polynomial-time $O(\sqrt n)$-approximation algorithms for (i) additive valuations, (ii) submodular valuations using value queries, and (iii) subadditive valuations using demand queries: there is one constant $C>0$ such that each algorithm outputs an allocation $A$ with
--   $$\mathrm{OPT}_{MM}\le C\sqrt n\cdot\min_iv_i(A_i)$$
--   with probability at least $3/4$.
--
--   In Lean: one $C>0$, constants $c,d$ and three coin-only programs, all fixed before the instance. For every $n\ge1$ and $m$: (i) for every table of nonnegative rationals $v_{ij}$ (no oracle), (ii) for every $\sigma$, every family of normalized monotone submodular valuations with values $a/b$, $a,b\le2^\sigma$, and every exact value oracle, (iii) for every $\sigma$, every family of normalized monotone subadditive valuations with the same bound and every ordinary demand oracle (any tie-breaking), every run halts within $c(1+\text{size})^d$ bit-cost work and, with probability at least $3/4$, the output allocation $A$ satisfies $\min_iv_i(Y_i)\le C\sqrt n\min_iv_i(A_i)$ for every allocation $Y$.
--
--   This is the paper's first headline result; the paper proves it with ratio $768\lceil\sqrt n\rceil$ for (i), (ii) and $24576\cdot2^{20}\lceil\sqrt n\rceil$ for (iii).
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: randomized O(√n)-approximation → probability at least 3/4 over the coins that OPT_MM ≤ C√n · min_i v_i(A_i); reason: the paper's proof (p. 33) gives probability ≥ 3/4 for every part; it implies the in-expectation reading
--   - encoding: OPT_MM → the comparator form: min_i v_i(Y_i) ≤ C√n · min_i v_i(A_i) for every allocation Y; reason: OPT_MM is the maximum of min_i v_i(Y_i) over allocations; same claim, no optimum given to the program
--   - reading: running time polynomial in the encoding of the valuation values (§2, p. 10) → valuation values are a/b with naturals a, b ≤ 2^σ, b ≠ 0, and σ is part of the input (size n + m + σ); reason: App. E.1 (p. 67) makes the §2 convention concrete with the known bound σ
--   - encoding: additive valuations given explicitly → the input n, m and the table (v_{ij}) of nonnegative rationals row by row, size n + m + its encoding length; v_i(S) = Σ_{j∈S} v_{ij}; no oracle; reason: an additive valuation is its table of item values
--   - encoding: value queries / demand queries → part (ii) runs with a value oracle only, part (iii) with an ordinary demand oracle only, part (i) with the empty oracle; reason: each part uses only its class's queries
--   - encoding: oracle queries with ties broken arbitrarily → an oracle is any fixed answer function correct on every well-formed question, quantified universally outside the probability over the coins; reason: the standard reading of 'ties broken arbitrarily'; malformed questions are unconstrained, so the program cannot rely on them
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: the returned allocation → the first m entries of the output list: entry j = i + 1 gives item j to agent i, any other value leaves j unassigned; reason: every output decodes to an allocation; nothing is excluded
--   - encoding: fair random bits → CoinOnly: the three programs never use the exact sampling instruction; reason: the paper's final algorithms use fair bits (p. 33, App. E.2)
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 4, Theorem 1.1 (proof p. 33)

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

open MultiAllocToAlloc.Subadditive

namespace SantaClausNSW.MaxMin

/-- **Theorem 1.1** (p. 4). There are one constant `C > 0`, constants `c, d` and three fair-coin
programs such that, for every `n ≥ 1` and `m` (and every `σ` in (ii), (iii)), every run halts
within `c (1 + size)^d` bit work and, with probability at least `3/4`, outputs an allocation `A`
with `min_i v_i(Y_i) ≤ C √n · min_i v_i(A_i)` for every allocation `Y`:
(i) additive valuations given by an explicit table `(v_{ij})` of nonnegative rationals, no oracle;
(ii) normalized monotone submodular valuations with values `a/b`, `a, b ≤ 2^σ`, through any exact
value oracle; (iii) normalized monotone subadditive valuations with the same bound, through any
ordinary demand oracle. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ (P₁ P₂ P₃ : Program) (c d : ℕ),
      CoinOnly P₁ ∧ CoinOnly P₂ ∧ CoinOnly P₃ ∧
      ∀ (n m : ℕ), 0 < n →
        (∀ V : Fin n → Fin m → ℚ, (∀ i j, 0 ≤ V i j) →
          HaltsWithin P₁ noOracle (tableInput V) (c * (1 + explicitSize n m (tableInput V)) ^ d) ∧
          outProb P₁ noOracle (tableInput V) (c * (1 + explicitSize n m (tableInput V)) ^ d)
            (fun l => MMApprox (tableValuation V) (C * Real.sqrt n) (decAlloc n m l)) ≥ 3 / 4) ∧
        (∀ (σ : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
          (∀ i, IsValuation (v i) ∧ IsSubmodular (v i)) → BitBounded v σ →
          ∀ O : Oracle, IsValueOracle v O →
            HaltsWithin P₂ O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d) ∧
            outProb P₂ O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d)
              (fun l => MMApprox v (C * Real.sqrt n) (decAlloc n m l)) ≥ 3 / 4) ∧
        (∀ (σ : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
          (∀ i, IsValuation (v i) ∧ IsSubadditive (v i)) → BitBounded v σ →
          ∀ O : Oracle, IsDemandOracle v O →
            HaltsWithin P₃ O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d) ∧
            outProb P₃ O (oracleInput n m σ) (c * (1 + oracleSize n m σ) ^ d)
              (fun l => MMApprox v (C * Real.sqrt n) (decAlloc n m l)) ≥ 3 / 4) := by sorry

end SantaClausNSW.MaxMin
