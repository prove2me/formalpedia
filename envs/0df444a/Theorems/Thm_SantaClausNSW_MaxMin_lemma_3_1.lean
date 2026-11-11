-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_1
-- name    : SantaClausNSW.MaxMin.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:53.828117+00:00
-- url     : https://prove2.me/theorems/f5b18933-abd0-4d7d-b4be-dbe84741103f
-- title:
--   Lemma 3.1 — the rounding lemma: configurations with their LP marginals and coefficient value τ for every agent with probability ≥ 3/4
-- statement:
--   In the setting of §3.1, suppose
--   $$\sum_{i}\sum_{S\in S_i}y_{i,S}\min\Big\{1,\Big(\frac{32\tau}{\mu_{i,S}}\Big)^3\Big\}\le\frac14,\tag{7}$$
--   the minimum read as $1$ when $\mu_{i,S}=0$. Then there is a randomized polynomial-time algorithm that, given the setting, selects a configuration $S_i\in C_i$ for each agent and returns an allocation $A_i\subseteq S_i$ such that, with probability at least $3/4$, $a^{i,S_i}(A_i)\ge\tau$ for every agent $i$; moreover $\Pr[S_i=S]=y_{i,S}$ for every agent $i$ and configuration $S$.
--
--   In Lean: one program and constants $c,d$, fixed before the instance, such that on every encoding of every such setting with $n\ge1$ every run halts within $c(1+\text{size})^d$ work, every run outputs $S_i\in C_i$ and $A_i\subseteq S_i$, and the probability and marginal claims hold. This is the engine of Theorem 3.5 and Corollary 3.8.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - reading: sampling calls of the rounding procedures → the program may also use the machine's exact rational sampling instruction; reason: App. E.2 (p. 67): 'In the rounding analyses, we sample exactly from explicitly given rational distributions'; exact non-dyadic marginals are impossible with boundedly many fair coins
--   - encoding: 'given' the setting → the input lists n, m, τ, K and one record (i, y_{i,S}, 1_S, a^{i,S}, 1_{S∈L_i}) per configuration of positive mass, in any order; size n + m + its encoding length; reason: an explicit solution is a list of triples (p. 11); the program must work for every order
--   - encoding: the returned allocation → the first m entries of the output list: entry j = i + 1 gives item j to agent i, any other value leaves j unassigned; reason: every output decodes to an allocation; nothing is excluded
--   - encoding: the selected configurations S_i → indicator blocks of the output after the allocation; reason: total decoding; S_i ∈ C_i is part of the conclusion
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 12, Lemma 3.1

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Rounding

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.1** (p. 12). There are a program (with exact rational sampling, App. E.2) and
constants `c, d` such that, on every encoding of a setting of §3.1 satisfying (7)
(`∑_i ∑_{S ∈ S_i} y_{i,S} min{1, (32τ/µ_{i,S})^3} ≤ 1/4`, the term read as `1` when
`µ_{i,S} = 0`), every run halts within `c (1 + size)^d` work and selects `S_i ∈ C_i` and
`A_i ⊆ S_i` (an allocation); with probability at least `3/4`, `a^{i,S_i}(A_i) ≥ τ` for every
agent `i`; and `Pr[S_i = S] = y_{i,S}` for every `i` and `S`. -/
theorem lemma_3_1 :
    ∃ (P : Program) (c d : ℕ), ∀ (n m : ℕ), 0 < n →
      ∀ st : Setting n m, st.Valid → st.Budget (1 / 4) →
      ∀ input : List ℚ, st.Encodes input →
        HaltsWithin P noOracle input (c * (1 + explicitSize n m input) ^ d) ∧
        (∀ s ∈ (run P noOracle (c * (1 + explicitSize n m input) ^ d + 1)
            (initState input)).support, ∀ i : Fin n,
          0 < st.y i (decConfigs n m (outList s.mem) i) ∧
          decAlloc n m (outList s.mem) i ⊆ decConfigs n m (outList s.mem) i) ∧
        outProb P noOracle input (c * (1 + explicitSize n m input) ^ d)
          (fun l => ∀ i : Fin n, st.τ ≤ st.coef i (decConfigs n m l i) (decAlloc n m l i))
          ≥ 3 / 4 ∧
        ∀ (i : Fin n) (S : Finset (Fin m)),
          outProb P noOracle input (c * (1 + explicitSize n m input) ^ d)
            (fun l => decConfigs n m l i = S) = (st.y i S : ℝ) := by sorry

end SantaClausNSW.MaxMin
