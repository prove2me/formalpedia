-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_theorem_3_5
-- name    : SantaClausNSW.MaxMin.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:37:02.567613+00:00
-- url     : https://prove2.me/theorems/4ef3823e-ef4e-4cb9-bb60-2b97a93be5cd
-- title:
--   Theorem 3.5 — with supporting clauses, every agent gets T/(128⌈√n⌉) with probability ≥ 3/4
-- statement:
--   Given a feasible configuration solution with objective value $T$ and a supporting clause (13) for every pair $(i,S)$ of its support, there is a randomized polynomial-time algorithm that finds an allocation $A$ in which every agent receives value
--   $$v_i(A_i)\ge\frac{T}{128\lceil\sqrt n\rceil}$$
--   with probability at least $3/4$. Applied to the solution of Lemma 3.4 it gives parts (i) and (ii) of Theorem 1.1 with ratio $768\lceil\sqrt n\rceil$.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: sampling calls of the rounding procedures → the program may also use the machine's exact rational sampling instruction; reason: App. E.2 (p. 67): 'In the rounding analyses, we sample exactly from explicitly given rational distributions'; exact non-dyadic marginals are impossible with boundedly many fair coins
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: 'given' the solution and the clauses → the input n, m, T, K and one record (i, y_{i,S}, 1_S, w^{i,S}) per configuration of positive mass, in any order, rational; size n + m + its encoding length; reason: an explicit solution is a list of triples (p. 11); the program must work for every order
--   - encoding: the returned allocation → the first m entries of the output list: entry j = i + 1 gives item j to agent i, any other value leaves j unassigned; reason: every output decodes to an allocation; nothing is excluded
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 18, Theorem 3.5

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Rounding

namespace SantaClausNSW.MaxMin

/-- **Theorem 3.5** (p. 18). There are a program (with exact rational sampling, App. E.2) and
constants `c, d` such that, given an explicit feasible configuration solution with objective
value `T ≥ 0` for normalized monotone valuations and a supporting clause (13) for every pair
`(i, S)` of its support, every run halts within `c (1 + size)^d` work and, with probability at
least `3/4`, outputs an allocation in which every agent receives value at least
`T/(128⌈√n⌉)`. -/
theorem theorem_3_5 :
    ∃ (P : Program) (c d : ℕ), ∀ (n m : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i)) →
      ∀ (y : Fin n → Finset (Fin m) → ℚ) (T : ℚ), 0 ≤ T →
        IsConfigSolutionAt v (fun i S => (y i S : ℝ)) (T : ℝ) →
      ∀ w : Fin n → Finset (Fin m) → Fin m → ℚ,
        (∀ i S, 0 < y i S → IsSupportingClause (v i) S (fun j => (w i S j : ℝ))) →
      ∀ input : List ℚ, EncodesClauses y w T input →
        HaltsWithin P noOracle input (c * (1 + explicitSize n m input) ^ d) ∧
        outProb P noOracle input (c * (1 + explicitSize n m input) ^ d)
          (fun l => ∀ i : Fin n,
            (T : ℝ) / (128 * (⌈Real.sqrt n⌉₊ : ℝ)) ≤ v i (decAlloc n m l i)) ≥ 3 / 4 := by sorry

end SantaClausNSW.MaxMin
