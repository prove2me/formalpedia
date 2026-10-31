-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_trace_young
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.trace_young
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:57:35.791995+00:00
-- url     : https://prove2.me/theorems/b12b88ee-14e4-463c-b9e5-917c928b40e3
-- title:
--   §3.1.1 (3.16): matrix trace Young inequality
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For positive M,N and conjugate p,q, p>1, Tr MN≤Tr M^p/p+Tr N^q/q, equality iff M^p=N^q; for 0<p<1 and M≪N reverse the inequality.
--
--   $$
--   \operatorname{Tr}(MN)\le\frac1p\operatorname{Tr}M^p+\frac1q\operatorname{Tr}N^q,\qquad\text{equality}\iff M^p=N^q.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 41, §3.1.1 (3.16): matrix trace Young inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#3.young
§3.1.1 (3.16): matrix trace Young inequality, arXiv:1504.00233v5, PDF p.41. -/
theorem trace_young [Nonempty I] (M N : paperMat I) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (p q : ℝ) (hp : 0 < p) (hq : q ≠ 0) (hc : 1/p+1/q = 1) :
    (1 < p → (M*N).trace.re ≤ (paperPower M p).trace.re/p+(paperPower N q).trace.re/q) ∧
    (1 < p → ((M*N).trace.re = (paperPower M p).trace.re/p+(paperPower N q).trace.re/q ↔ paperPower M p = paperPower N q)) ∧
    (p < 1 → paperSupported M N → (paperPower M p).trace.re/p+(paperPower N q).trace.re/q ≤ (M*N).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
