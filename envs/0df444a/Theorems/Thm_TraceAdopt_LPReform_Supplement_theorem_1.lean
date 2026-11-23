-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_Supplement_theorem_1
-- name    : TraceAdopt.LPReform.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:49:12.933861+00:00
-- url     : https://prove2.me/theorems/97d4dad4-2963-411a-824e-8f62779d9e71
-- title:
--   Theorem 1, p. 11 — DEC-SCTM is in P for $\theta\le2$ and NP-hard for every fixed $3\le\theta\le k$
-- statement:
--   Let $\mathrm{DEC\text{-}SCTM}_{k,\theta}$ be the decision problem of Definition 1: on a connected hypergraph whose supply chains all have $k$ firms and threshold $\theta$, with all benefits $r_{ji}$ and adoption costs $c_i$ equal to one and with rational seeding costs $w_i$, is there a seed set of cost at most an integer $h$ that leads to full SCTM activation?
--
--   **Theorem 1.** The complexity of DEC-SCTM depends on $k$ and $\theta$ as in the following table (cells with $\theta>k$ are empty):
--
--   | $\theta$ / $k$ | $k=1$ | $k=2$ | $k=3$ | $k\ge4$ |
--   |---|---|---|---|---|
--   | $\theta=1$ | in P | in P | in P | in P |
--   | $\theta=2$ |  | in P | in P | in P |
--   | $\theta=3$ |  |  | NP-hard | NP-hard |
--   | $\theta\ge4$ |  |  |  | NP-hard |
--
--   Equivalently:
--
--   1. $\mathrm{DEC\text{-}SCTM}_{k,1}\in\mathrm P$ for every $k\ge1$;
--   2. $\mathrm{DEC\text{-}SCTM}_{k,2}\in\mathrm P$ for every $k\ge2$;
--   3. $\mathrm{DEC\text{-}SCTM}_{k,\theta}$ is NP-hard for every fixed pair with $3\le\theta\le k$:
--
--   $$L\le_p \mathrm{DEC\text{-}SCTM}_{k,\theta}\quad\text{for every }L\in\mathrm{NP}.$$
--
--   The theorem says that as soon as supply chains contain three or more firms and at least three are needed for traceability benefits, there is no polynomial-time algorithm for MIN-SCTM unless P = NP, while the problem is easy when one or two adopters suffice.
--
--   **Formalization Note** P is Cook's class `CookPvsNP.P Bool` (a one-tape Turing machine deciding the language in time $|s|^d+d$), and NP-hardness is the published `KingTerrain.NPHard.IsNPHard` (polynomial-time many-one reductions from every NP language over every finite nonempty alphabet). Inputs are binary codes as in `DecSCTM`: the deciders of items 1 and 2 must also reject non-codes and invalid inputs, and the seeding costs are arbitrary rationals, negative ones included.
--
--   Differences from the source:
--   - encoding: in P → membership in CookPvsNP.P Bool (a one-tape Turing machine deciding the language within |s|^d + d steps); reason: Cook's definition of P, the published platform definition
--   - encoding: NP-hard → KingTerrain.NPHard.IsNPHard: every NP language over every finite nonempty alphabet (Cook's one-tape Turing machines) is polynomial-time many-one reducible to the language; reason: the standard notion; the published definition adds no NP-membership requirement, and the paper claims none
--   - reading: table with blank cells (θ = 2, k = 1; θ = 3, k ≤ 2; θ ≥ 4, k ≤ θ − 1) → three conjuncts: θ = 1 for every k ≥ 1; θ = 2 for every k ≥ 2; NP-hard for every 3 ≤ θ ≤ k; reason: the nonblank cells are exactly these; blank cells (θ > k) are excluded by the standing assumption θ_j ≤ k_j and make no claim
--   - reading: hypergraph G as defined in Section 3, whose standing assumption is θ_j ∈ {2,...,k_j} → θ_j ≥ 2 is not imposed; reason: the theorem's table has a row θ = 1, so Definition 1 overrides that standing assumption for this theorem
--   - encoding: DEC-SCTM input (integer h, hypergraph G, rational w_i) → the language decSCTM k θ ⊆ {0,1}* of binary codes (self-delimiting binary numerals for n, m, each hyperedge as its size and sorted members, each w_i as reduced signed numerator and positive denominator, h in sign-magnitude); words that are not the code of a valid input are rejected; reason: complexity classes are defined on languages; the code is length-faithful, so polynomial time on codes is polynomial time in the bit size of the input
--   - encoding: hypergraph G as defined in Section 3 (connected, all nodes can become active), with r_ji = c_i = 1, k_j = k, θ_j = θ → DecInput.Valid k: every hyperedge has exactly k firms, the auxiliary graph G′ is connected, every firm lies in some hyperedge; the instance has r = c = 1 and θ_j = θ; reason: with r_ji = c_i = 1 the standing assumption c_i ≤ Σ_{j∋i} r_ji says exactly that each firm lies in a chain; connectivity is read through G′ as in the published model
--   - encoding: for all i = 0,...,n → firms Fin n (n firms); reason: the index 0 is a slip for N_F = {1,...,n} (p. 5); no extra firm is created
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 11, Theorem 1 (proof p. 36, Appendix B.2; Definition 1 p. 11)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Supplement_DecSCTM
import Definitions.Def_KingTerrain_NPHard_Complexity

namespace TraceAdopt.LPReform.Supplement

/-- Theorem 1, p. 11: the complexity of DEC-SCTM by chain size `k` and threshold `θ`.
Row `θ = 1`: in P for every `k ≥ 1`. Row `θ = 2`: in P for every `k ≥ 2`.
Rows `θ = 3` and `θ ≥ 4`: NP-hard for every `k ≥ θ`. Cells with `θ > k` are blank. -/
theorem theorem_1 :
    (∀ k : ℕ, 1 ≤ k → decSCTM k 1 ∈ CookPvsNP.P Bool) ∧
    (∀ k : ℕ, 2 ≤ k → decSCTM k 2 ∈ CookPvsNP.P Bool) ∧
    (∀ k θ : ℕ, 3 ≤ θ → θ ≤ k → KingTerrain.NPHard.IsNPHard (decSCTM k θ)) := by sorry

end TraceAdopt.LPReform.Supplement
