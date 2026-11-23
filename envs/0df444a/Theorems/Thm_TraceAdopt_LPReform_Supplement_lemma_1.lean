-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_Supplement_lemma_1
-- name    : TraceAdopt.LPReform.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:48:39.057804+00:00
-- url     : https://prove2.me/theorems/8b96ce06-9563-464d-8323-c6fb191bb03e
-- title:
--   Lemma 1, p. 35 — DEC-SCTM is NP-hard for $k=3$, $\theta=3$
-- statement:
--   Consider DEC-SCTM (Definition 1) with every supply chain of size $k=3$ and threshold $\theta=3$: all benefits and adoption costs equal one, so a firm adopts as soon as one of its chains has two other active firms, and the question is whether some seed set of total rational cost at most $h$ fully activates the connected hypergraph.
--
--   **Lemma 1.** The language $\mathrm{DEC\text{-}SCTM}_{3,3}$ is NP-hard:
--
--   $$L\le_p \mathrm{DEC\text{-}SCTM}_{3,3}\qquad\text{for every } L\in\mathrm{NP}.$$
--
--   This is the base case of the hardness part of Theorem 1, from which the cases $3\le\theta\le k$ follow by padding.
--
--   **Formalization Note** NP-hardness is the published `KingTerrain.NPHard.IsNPHard`: every NP language, over every finite nonempty alphabet, reduces to the language by a polynomial-time many-one reduction computed by a one-tape Turing machine (Cook's definitions, `CookPvsNP`). Inputs are binary codes as in `DecSCTM`; non-codes and invalid inputs are NO instances.
--
--   Differences from the source:
--   - encoding: NP-hard → KingTerrain.NPHard.IsNPHard: every NP language over every finite nonempty alphabet (Cook's one-tape Turing machines) is polynomial-time many-one reducible to the language; reason: the standard notion; the published definition adds no NP-membership requirement, and the paper claims none
--   - encoding: DEC-SCTM input (integer h, hypergraph G, rational w_i) → the language decSCTM k θ ⊆ {0,1}* of binary codes (self-delimiting binary numerals for n, m, each hyperedge as its size and sorted members, each w_i as reduced signed numerator and positive denominator, h in sign-magnitude); words that are not the code of a valid input are rejected; reason: complexity classes are defined on languages; the code is length-faithful, so polynomial time on codes is polynomial time in the bit size of the input
--   - encoding: hypergraph G as defined in Section 3 (connected, all nodes can become active), with r_ji = c_i = 1, k_j = k, θ_j = θ → DecInput.Valid k: every hyperedge has exactly k firms, the auxiliary graph G′ is connected, every firm lies in some hyperedge; the instance has r = c = 1 and θ_j = θ; reason: with r_ji = c_i = 1 the standing assumption c_i ≤ Σ_{j∋i} r_ji says exactly that each firm lies in a chain; connectivity is read through G′ as in the published model
--   - encoding: for all i = 0,...,n → firms Fin n (n firms); reason: the index 0 is a slip for N_F = {1,...,n} (p. 5); no extra firm is created
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 35, Lemma 1 (proof pp. 35–36, building blocks p. 34, Appendix B.1)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Supplement_DecSCTM
import Definitions.Def_KingTerrain_NPHard_Complexity

namespace TraceAdopt.LPReform.Supplement

/-- Lemma 1, p. 35: DEC-SCTM is NP-hard when `k = 3` and `θ = 3`. -/
theorem lemma_1 : KingTerrain.NPHard.IsNPHard (decSCTM 3 3) := by sorry

end TraceAdopt.LPReform.Supplement
