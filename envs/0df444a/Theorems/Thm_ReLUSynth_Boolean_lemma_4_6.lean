-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_6
-- name    : ReLUSynth.Boolean.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:27.530627+00:00
-- url     : https://prove2.me/theorems/307e5618-2399-44a1-b677-f6c67dd588df
-- title:
--   Lemma 4.6 — uniform specialization: an exact Boolean output of a cap-four candidate is a formal Laurent identity in w, Γ
-- statement:
--   Consider the calibrated inventory of §4.2. Fix any legal candidate with at most four computational vertices and any Boolean input $x$. Freeze the network at its actual activation pattern at $x$ (each hidden ReLU replaced by its affine preactivation if that is positive, by $0$ otherwise), and expand its output as a Laurent polynomial in two formal variables $w,\Gamma$ over $\mathbb Q$, replacing every parameter occurrence by the formal expansion of its value. If the numerical output at $x$ is $b\in\{0,1\}$, the expanded Laurent polynomial is identically $b$:
--   $$N(x)=b\ \Longrightarrow\ \widetilde N_{\eta(x)}(x)\equiv b\quad\text{in }\mathbb Q[w^{\pm1},\Gamma^{\pm1}].$$
--   This holds uniformly for every legal assignment of occurrences and every Boolean input.
--
--   It turns each exact Boolean output equation into coefficient identities, used throughout the placement argument.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - generalization: an instance in the hardness family produced by Lemma 4.5 (p. 19) → any instance satisfying every restriction listed in Lemma 4.5 (CalibData.Valid: q ≥ 5 prime, 0 < β_j < T, β_j not a power of two, β_j ≡ 3, T ≡ 0 (mod q), n > p); reason: the proofs on pp. 19–27 and in Appendix A use only these restrictions; every instance the reduction produces satisfies them, so the Lean statement specializes to the paper's
--   - reading: choose an odd prime r, powers of two F and M satisfying the displayed inequalities (pp. 19–20) → every choice of r, F, M satisfying those inequalities (strictly, as printed); reason: the page leaves the choice free among the values satisfying the inequalities, and its lemmas are claimed for the construction so chosen
--   - encoding: a candidate / legal assignment (in §4 and Appendix A, legal = at-most-once, p. 10) with computational-node cap four → Net.Permitted InventoryRule.atMostOnce 4 on the occurrence type Occ c of the calibrated inventory; reason: exactly-once networks are among these, as the paper notes (p. 10)
--   - encoding: a Laurent polynomial in formal variables w, Γ with rational coefficients → Laurent2 = AddMonoidAlgebra ℚ (ℤ × ℤ), the monomial w^i Γ^j being single (i, j) 1; reason: the group algebra of ℤ² is exactly the two-variable Laurent polynomial ring
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 21, Lemma 4.6

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma 4.6 (p. 21): for the calibrated inventory, any legal candidate with at most four
computational vertices and any Boolean input `x`: if the numerical output at `x` is `b ∈ {0,1}`,
then the output of the network frozen at its actual activation pattern at `x`, expanded with the
formal expansions of the occurrences as a Laurent polynomial in `w, Γ`, is identically `b`. -/
theorem lemma_4_6 (c : CalibData) (hc : c.Valid) (N : Net (Coord c) (Occ c))
    (hN : N.Permitted InventoryRule.atMostOnce 4) (x : Coord c → Bool) (b : Bool)
    (hout : N.eval c.invR (boolVec x) = bitR b) :
    N.frozenEval c.formal (N.actPattern c.invR (boolVec x))
        (fun t => if x t then (1 : Laurent2) else 0) =
      (if b then (1 : Laurent2) else 0) := by sorry

end ReLUSynth.Boolean
