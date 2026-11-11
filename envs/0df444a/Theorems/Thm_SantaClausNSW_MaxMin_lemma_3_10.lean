-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_10
-- name    : SantaClausNSW.MaxMin.lemma_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:37:15.927344+00:00
-- url     : https://prove2.me/theorems/864d1190-aead-4406-af54-6882d370e573
-- title:
--   Lemma 3.10 — conditional guiding-tree rounding: marginals y and value v_i(S)/2 with conditional probability ≥ 1/4
-- statement:
--   Let $(v_i)$ be normalized monotone subadditive valuations, and for each agent $i$ let an explicit distribution over configurations be given (configuration $S$ with probability $y_{i,S}$, the empty configuration allowed) with
--   $$\sum_i\sum_{S\ni j}y_{i,S}\le\frac12\qquad(j\in M).$$
--   There is a randomized guiding-tree rounding procedure that selects configurations $S_i$ with $\Pr[S_i=S]=y_{i,S}$ and returns a feasible allocation $G$ with $G_i\subseteq S_i$ such that, for every $i$ and every $S$ with $y_{i,S}>0$,
--   $$\Pr\Big[v_i(G_i)\ge\frac{v_i(S)}2\ \Big|\ S_i=S\Big]\ge\frac14 .$$
--   It uses no valuation queries and only polynomially many combinatorial operations and sampling calls. Lemma 3.11 runs it $h$ times.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: sampling calls of the rounding procedures → the program may also use the machine's exact rational sampling instruction; reason: App. E.2 (p. 67): 'In the rounding analyses, we sample exactly from explicitly given rational distributions'; exact non-dyadic marginals are impossible with boundedly many fair coins
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: 'uses no valuation queries' → the program runs with the empty oracle (every answer is the empty list); reason: no information about the valuations is available to it
--   - encoding: explicit distributions → the input n, m, K and one triple (i, y_{i,S}, 1_S) per configuration of positive mass, in any order; size n + m + its encoding length; reason: an explicit distribution lists its rational probabilities
--   - encoding: polynomially many combinatorial operations and sampling calls → every run halts within c·(1 + size)^d bit-cost work, which bounds both; reason: each operation and each sampling call costs at least one unit of work
--   - encoding: the returned allocation → the first m entries of the output list: entry j = i + 1 gives item j to agent i, any other value leaves j unassigned; reason: every output decodes to an allocation; nothing is excluded
--   - encoding: Pr[· | S_i = S] → Pr[· ∧ S_i = S] / Pr[S_i = S]; reason: the definition of conditional probability; Pr[S_i = S] = y_{i,S} > 0
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), pp. 25–26, Lemma 3.10

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Rounding

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.10** (p. 25). There are a program (with exact rational sampling, no valuation
queries) and constants `c, d` such that, for normalized monotone subadditive valuations and
explicit distributions `y_i` over configurations (the empty configuration allowed) with
`∑_i ∑_{S ∋ j} y_{i,S} ≤ 1/2` for every item `j`, every run halts within `c (1 + size)^d` work
and selects configurations `S_i` and a feasible allocation `G` with `G_i ⊆ S_i`;
`Pr[S_i = S] = y_{i,S}`; and `Pr[v_i(G_i) ≥ v_i(S)/2 | S_i = S] ≥ 1/4` for every `i` and every
`S` with `y_{i,S} > 0`. -/
theorem lemma_3_10 :
    ∃ (P : Program) (c d : ℕ), ∀ (n m : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i) ∧ IsSubadditive (v i)) →
      ∀ y : Fin n → Finset (Fin m) → ℚ, (∀ i S, 0 ≤ y i S) → (∀ i, ∑ S, y i S = 1) →
        (∀ j : Fin m, ∑ i : Fin n,
          ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin m) => j ∈ S), (y i S : ℝ) ≤ 1 / 2) →
      ∀ input : List ℚ, EncodesDistributions y input →
        HaltsWithin P noOracle input (c * (1 + explicitSize n m input) ^ d) ∧
        (∀ s ∈ (run P noOracle (c * (1 + explicitSize n m input) ^ d + 1)
            (initState input)).support, ∀ i : Fin n,
          0 < y i (decConfigs n m (outList s.mem) i) ∧
          decAlloc n m (outList s.mem) i ⊆ decConfigs n m (outList s.mem) i) ∧
        (∀ (i : Fin n) (S : Finset (Fin m)),
          outProb P noOracle input (c * (1 + explicitSize n m input) ^ d)
            (fun l => decConfigs n m l i = S) = (y i S : ℝ)) ∧
        ∀ (i : Fin n) (S : Finset (Fin m)), 0 < y i S →
          condProbOf (run P noOracle (c * (1 + explicitSize n m input) ^ d + 1)
              (initState input))
            (fun s => v i S / 2 ≤ v i (decAlloc n m (outList s.mem) i))
            (fun s => decConfigs n m (outList s.mem) i = S) ≥ 1 / 4 := by sorry

end SantaClausNSW.MaxMin
