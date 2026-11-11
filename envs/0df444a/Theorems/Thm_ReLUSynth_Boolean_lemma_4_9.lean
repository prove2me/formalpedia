-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_9
-- name    : ReLUSynth.Boolean.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:39.871861+00:00
-- url     : https://prove2.me/theorems/24c27b54-6d63-444c-b9a1-0dab559c9977
-- title:
--   Lemma 4.9 — a cap-four network representing the calibrated target yields a common-ramp network representing it
-- statement:
--   Let $W,f$ be the calibrated inventory and target, with computational-node cap four and affine output. If some permitted network represents $f$ on the Boolean cube, then some permitted network using a submultiset of the same occurrences has the **common-ramp** form
--   $$N(x)=D\big(\rho(S(x)-(P-w))-\rho(S(x)-P)\big),\qquad S(x)=a\,u(x)+\sum_{j=1}^d b_jx_j,$$
--   and also represents $f$. Here $D=M$; the coefficients $a,b_j,v_b,v_j$ are zero (absent) or a single positive inventory primitive; the optional sharing wire $u(x)=\rho(v_b+\sum_jv_jx_j)$ enters each hinge through one sharing edge of weight $a$, and each input enters each hinge through one direct edge of weight $b_j$; each nonzero $a$ and $b_j$ uses two identical-value occurrences; the hinge biases $-(P-w),-P$ and gains $\pm D$ use their supplied occurrences; there is no output bias, skip edge or wire-to-output edge; a wire without parameters or without sharing edge is omitted.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - generalization: an instance in the hardness family produced by Lemma 4.5 (p. 19) → any instance satisfying every restriction listed in Lemma 4.5 (CalibData.Valid: q ≥ 5 prime, 0 < β_j < T, β_j not a power of two, β_j ≡ 3, T ≡ 0 (mod q), n > p); reason: the proofs on pp. 19–27 and in Appendix A use only these restrictions; every instance the reduction produces satisfies them, so the Lean statement specializes to the paper's
--   - reading: choose an odd prime r, powers of two F and M satisfying the displayed inequalities (pp. 19–20) → every choice of r, F, M satisfying those inequalities (strictly, as printed); reason: the page leaves the choice free among the values satisfying the inequalities, and its lemmas are claimed for the construction so chosen
--   - encoding: a candidate / legal assignment (in §4 and Appendix A, legal = at-most-once, p. 10) with computational-node cap four → Net.Permitted InventoryRule.atMostOnce 4 on the occurrence type Occ c of the calibrated inventory; reason: exactly-once networks are among these, as the paper notes (p. 10)
--   - reading: some permitted network using a submultiset of the same occurrences has the form D(ρ(S−(P−w))−ρ(S−P)) → … has that form and represents f on the Boolean cube; reason: as printed the conclusion holds trivially (a = b_j = 0); the proof (Lemma A.19, p. 107) and its use in Theorem 4.12 (p. 27) need the clause; INSIGHTS I1
--   - encoding: a permitted network of the displayed form using a submultiset of the occurrences → CommonRamp c with Legal (its toNet is permitted at-most-once with cap four, positivity, paired values, wire omitted without sharing edge), toNet laying out wire, two hinges and output; reason: toNet is exactly the displayed network; permittedness under at-most-once is use of a submultiset
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, pp. 23–24, Lemma 4.9

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma 4.9 (pp. 23–24), with the reading of INSIGHTS I1: for the calibrated inventory and
target with cap four and affine output, if some permitted network represents `f` on the Boolean
cube, then some legal common-ramp network `D(ρ(S(x) − (P − w)) − ρ(S(x) − P))`,
`S(x) = a·u(x) + ∑_j b_j x_j`, on a submultiset of the same occurrences also represents `f`. -/
theorem lemma_4_9 (c : CalibData) (hc : c.Valid)
    (hrep : ∃ N : Net (Coord c) (Occ c), N.Permitted InventoryRule.atMostOnce 4 ∧
      ∀ x : Coord c → Bool, N.eval c.invR (boolVec x) = bitR (c.target x)) :
    ∃ C : CommonRamp c, C.Legal ∧
      ∀ x : Coord c → Bool, C.toNet.eval c.invR (boolVec x) = bitR (c.target x) := by sorry

end ReLUSynth.Boolean
