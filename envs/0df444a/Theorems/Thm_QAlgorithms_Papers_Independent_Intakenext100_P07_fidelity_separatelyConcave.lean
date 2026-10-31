-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_fidelity_separatelyConcave
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.fidelity_separatelyConcave
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:01:05.460295+00:00
-- url     : https://prove2.me/theorems/f386bb36-e362-4852-8b22-35d752302e92
-- title:
--   3.11
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   Squared algebraic fidelity is concave in either positive-operator argument separately.
--
--   $$
--   \lambda F(\rho,\sigma)+(1-\lambda)F(\tau,\sigma)\le F(\lambda\rho+(1-\lambda)\tau,\sigma),
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 45, 3.11

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

/-- NODE paper:1504.00233#3.11
3.11, arXiv:1504.00233v5, PDF p.45. -/
theorem fidelity_separatelyConcave [Nonempty I] (r s t : paperMat I) (hr : r.PosSemidef) (hs : s.PosSemidef) (ht : t.PosSemidef)
    (a : ℝ) (ha : a ∈ Set.Icc 0 1) :
    a*paperFidelity r t+(1-a)*paperFidelity s t ≤ paperFidelity (paperMix a r s) t ∧
    a*paperFidelity t r+(1-a)*paperFidelity t s ≤ paperFidelity t (paperMix a r s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
