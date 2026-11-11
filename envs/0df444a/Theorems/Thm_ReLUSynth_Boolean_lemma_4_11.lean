-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_11
-- name    : ReLUSynth.Boolean.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:13:05.984729+00:00
-- url     : https://prove2.me/theorems/51f2d201-fa33-4dde-a998-420579bb5b95
-- title:
--   Lemma 4.11 — a legal common-ramp network equal to f exists iff the source instance has an exact-sum blocker of size ≤ p
-- statement:
--   For the calibrated construction, there exists a legal common-ramp network
--   $$N(x)=D\big(\rho(S(x)-(P-w))-\rho(S(x)-P)\big),\qquad S(x)=a\,u(x)+\sum_jb_jx_j,$$
--   following the positive-primitive and paired-occurrence conventions of Lemma 4.9 (optional sharing wire $u$, sharing and direct weights each zero or a single positive inventory primitive), that equals $f$ on all Boolean inputs, if and only if the source instance $\beta_1,\dots,\beta_n,T$ has an exact-sum blocker of size at most $p$. This includes the case in which no source subset sums to $T$, and allows an omitted sharing wire.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - generalization: an instance in the hardness family produced by Lemma 4.5 (p. 19) → any instance satisfying every restriction listed in Lemma 4.5 (CalibData.Valid: q ≥ 5 prime, 0 < β_j < T, β_j not a power of two, β_j ≡ 3, T ≡ 0 (mod q), n > p); reason: the proofs on pp. 19–27 and in Appendix A use only these restrictions; every instance the reduction produces satisfies them, so the Lean statement specializes to the paper's
--   - reading: choose an odd prime r, powers of two F and M satisfying the displayed inequalities (pp. 19–20) → every choice of r, F, M satisfying those inequalities (strictly, as printed); reason: the page leaves the choice free among the values satisfying the inequalities, and its lemmas are claimed for the construction so chosen
--   - encoding: a legal common-ramp network with the conventions of Lemma 4.9 → CommonRamp c with Legal and its network toNet; reason: the same object as in Lemma 4.9
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 25, Lemma 4.11

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Blocker
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma 4.11 (p. 25): for the calibrated construction, a legal common-ramp network equal to `f`
on all Boolean inputs exists if and only if the source instance `β_1, …, β_n, T` has an exact-sum
blocker of size at most `p`. -/
theorem lemma_4_11 (c : CalibData) (hc : c.Valid) :
    (∃ C : CommonRamp c, C.Legal ∧
      ∀ x : Coord c → Bool, C.toNet.eval c.invR (boolVec x) = bitR (c.target x)) ↔
    ∃ H : Finset (Fin c.n), IsBlocker c.β c.T c.p H := by sorry

end ReLUSynth.Boolean
