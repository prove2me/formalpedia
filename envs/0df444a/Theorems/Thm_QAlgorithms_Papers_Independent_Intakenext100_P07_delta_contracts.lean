-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_delta_contracts
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.delta_contracts
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:00:10.812676+00:00
-- url     : https://prove2.me/theorems/d8a4ae28-a00c-4c87-bc47-9ae09537d2ab
-- title:
--   3.8
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For arbitrary complex trace-class matrices ξ,ζ, and any CPTNI map F, Δ(Fξ,Fζ)≤Δ(ξ,ζ); Δ is the positive-cone dual norm of the difference, not merely half trace norm.
--
--   $$
--   \Delta(\mathcal F(\xi),\mathcal F(\zeta))\le\Delta(\xi,\zeta).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 44, 3.8

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

/-- NODE paper:1504.00233#3.8
3.8, arXiv:1504.00233v5, PDF p.44. -/
theorem delta_contracts [Nonempty I] [Nonempty J] (E : paperMat I →ₗ[ℂ] paperMat J) (hE : CPTNI E) (M N : paperMat I) :
    paperDelta (E M) (E N) ≤ paperDelta M N := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
