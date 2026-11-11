-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_A_2
-- name    : SantaClausNSW.MaxMin.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:35:57.519897+00:00
-- url     : https://prove2.me/theorems/48d8dddd-00be-44f4-ab17-8a72baf0ffff
-- title:
--   Lemma A.2 — ordinary demand queries implement the budgeted routine with β = 1/3 for subadditive valuations
-- statement:
--   For normalized monotone subadditive valuations, ordinary demand queries implement the budgeted routine of Lemma A.1 with $\beta=1/3$: there is a polynomial-time algorithm that, given an agent $i$, nonnegative rational costs $c$, a budget $B\ge0$ and a target $t>0$, and using only demand queries, returns a set $D$ with $c(D)\le B$ such that
--   $$\exists S:\ c(S)\le B,\ v_i(S)\ge t\quad\Longrightarrow\quad v_i(D)\ge t/3 .$$
--   Together with Appendix B and Lemma A.1 this gives Lemma 3.4 for subadditive valuations.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: running time polynomial in the encoding of the valuation values (§2, p. 10) → valuation values are a/b with naturals a, b ≤ 2^σ, b ≠ 0, and σ is part of the input (size n + m + σ); reason: App. E.1 (p. 67) makes the §2 convention concrete with the known bound σ
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: oracle queries with ties broken arbitrarily → an oracle is any fixed answer function correct on every well-formed question, quantified universally outside the probability over the coins; reason: the standard reading of 'ties broken arbitrarily'; malformed questions are unconstrained, so the program cannot rely on them
--   - encoding: the routine's input (costs, budget, target) → the input n, m, σ, i, c_1, …, c_m, B, t with rational c ≥ 0, B ≥ 0, t > 0; size n + m + σ + its encoding length; reason: Lemma A.1's routine takes exactly these rational data
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 61, Lemma A.2

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-- **Lemma A.2** (p. 61). Ordinary demand queries implement the budgeted routine of Lemma A.1
with `β = 1/3`: there are a program and constants `c, d` such that, for normalized monotone
subadditive valuations with values `a/b`, `a, b ≤ 2^σ`, every correct demand oracle, every agent
`i`, nonnegative rational costs `c_j`, a rational budget `B ≥ 0` and a rational target `t > 0`,
every run halts within `c (1 + size)^d` work and returns a set `D` with `c(D) ≤ B` and
`v_i(D) ≥ t/3` whenever some set `S` with `c(S) ≤ B` has `v_i(S) ≥ t`. -/
theorem lemma_A_2 :
    ∃ (P : Program) (c d : ℕ), ∀ (n m σ : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i) ∧ IsSubadditive (v i)) →
      BitBounded v σ → ∀ O : Oracle, IsDemandOracle v O →
      ∀ (i : Fin n) (cost : Fin m → ℚ) (Bud t : ℚ), (∀ j, 0 ≤ cost j) → 0 ≤ Bud → 0 < t →
        HaltsWithin P O (oracleInput n m σ ++ (((i : ℕ) : ℚ) :: (List.ofFn cost ++ [Bud, t])))
          (c * (1 + σ + explicitSize n m
            (oracleInput n m σ ++ (((i : ℕ) : ℚ) :: (List.ofFn cost ++ [Bud, t])))) ^ d) ∧
        ∀ s ∈ (run P O (c * (1 + σ + explicitSize n m
            (oracleInput n m σ ++ (((i : ℕ) : ℚ) :: (List.ofFn cost ++ [Bud, t])))) ^ d + 1)
            (initState (oracleInput n m σ ++ (((i : ℕ) : ℚ) :: (List.ofFn cost ++ [Bud, t]))))).support,
          ∑ j ∈ decSetAt m (outList s.mem) 0, cost j ≤ Bud ∧
          ((∃ S : Finset (Fin m), ∑ j ∈ S, cost j ≤ Bud ∧ (t : ℝ) ≤ v i S) →
            (t : ℝ) / 3 ≤ v i (decSetAt m (outList s.mem) 0)) := by sorry

end SantaClausNSW.MaxMin
