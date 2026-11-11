-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_A_1
-- name    : SantaClausNSW.MaxMin.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:19.853562+00:00
-- url     : https://prove2.me/theorems/7452b2fd-e41f-4ad4-986a-9b85b96d6a81
-- title:
--   Lemma A.1 — a β-approximate budgeted routine and exact values give a configuration solution with T > β T_LP/(1 + η)
-- statement:
--   Fix a rational $\beta\in(0,1]$. Suppose a polynomial-time routine takes nonnegative rational item costs $c$, a budget $B$ and a target $t>0$ and returns a set $D$ with $c(D)\le B$ and $v_i(D)\ge\beta t$ whenever some set within the budget has value at least $t$; suppose also that $v_i(S)$ can be evaluated exactly. Then for every rational $\eta>0$ one can either detect that $T_{LP}=0$ or compute an explicit configuration solution supported on polynomially many configurations at a target
--   $$T>\frac{\beta}{1+\eta}\,T_{LP},$$
--   in time polynomial in the input encoding length and $1/\eta$ for fixed $\beta$. With $\beta=1/3$, $\eta=1$ this is Lemma 3.4.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: 'Suppose there is a polynomial-time routine … Assume also that v_i(S) can be evaluated exactly' → an oracle port answering routine questions (i, c, B, t) with any set meeting the routine's guarantee, and exact value questions (i, S); each call is charged its question and answer bits; reason: the lemma is a reduction; a polynomial-time routine composes with a polynomial number of calls, so charging calls by their encoding is the same polynomial claim
--   - reading: running time polynomial in the encoding of the valuation values (§2, p. 10) → valuation values are a/b with naturals a, b ≤ 2^σ, b ≠ 0, and σ is part of the input (size n + m + σ); reason: App. E.1 (p. 67) makes the §2 convention concrete with the known bound σ
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: polynomial in the input encoding length and 1/η → work ≤ c·(1 + n + m + σ + |η| + ⌈1/η⌉)^d; reason: |η| is the bit length of η; ⌈1/η⌉ is the 1/η term
--   - encoding: an explicit configuration solution supported on polynomially many configurations → an output list of at most c·(1 + size)^d triples (i, y_{i,S}, 1_S), well-formed, forming a configuration solution with objective value T; reason: the paper's explicit format (p. 11) with the same polynomial as the time bound
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 59, Lemma A.1

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-- **Lemma A.1** (p. 59). Fix a rational `β ∈ (0, 1]`. There are a program and constants `c, d`
such that, for all normalized monotone valuations with values `a/b`, `a, b ≤ 2^σ`, every oracle
answering exact value queries and implementing a budgeted routine with factor `β`, and every
rational `η > 0`, every run on input `n, m, σ, η` halts within
`c (1 + n + m + σ + |η| + ⌈1/η⌉)^d` work and either reports `T_LP = 0` (and then `T_LP = 0`) or
outputs an explicit configuration solution with objective value `T`, supported on at most that
many configurations, with `T > β/(1 + η) · T_LP`. -/
theorem lemma_A_1 (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ (P : Program) (c d : ℕ), ∀ (n m σ : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i)) → BitBounded v σ →
      ∀ O : Oracle, IsBudgetedOracle v β O → ∀ η : ℚ, 0 < η →
        HaltsWithin P O (oracleInput n m σ ++ [η])
          (c * (1 + oracleSize n m σ + bitSizeQ η + ⌈(1 / η : ℚ)⌉₊) ^ d) ∧
        ∀ s ∈ (run P O (c * (1 + oracleSize n m σ + bitSizeQ η + ⌈(1 / η : ℚ)⌉₊) ^ d + 1)
            (initState (oracleInput n m σ ++ [η]))).support,
          SolOutcome v ((β : ℝ) / (1 + (η : ℝ)))
            (c * (1 + oracleSize n m σ + bitSizeQ η + ⌈(1 / η : ℚ)⌉₊) ^ d) (outList s.mem) := by sorry

end SantaClausNSW.MaxMin
