-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_purified_delta_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.purified_delta_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:03:18.091519+00:00
-- url     : https://prove2.me/theorems/133c382b-f724-483b-9b1a-6b00ba01a90e
-- title:
--   3.17
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For subnormalized ρ,τ, Δ(ρ,τ)≤P(ρ,τ)≤sqrt(2Δ(ρ,τ)−Δ(ρ,τ)^2)≤sqrt(2Δ(ρ,τ)).
--
--   $$
--   \Delta(\rho,\tau)\le P(\rho,\tau)\le\sqrt{2\Delta(\rho,\tau)-\Delta(\rho,\tau)^2}\le\sqrt{2\Delta(\rho,\tau)}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 48, 3.17

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

/-- NODE paper:1504.00233#3.17
3.17, arXiv:1504.00233v5, PDF p.48,49. -/
theorem purified_delta_bounds [Nonempty I] (r s : paperMat I) (hr : paperSubnormalized r) (hs : paperSubnormalized s) :
    paperDelta r s ≤ purified r s ∧ purified r s ≤ Real.sqrt (2*paperDelta r s-paperDelta r s^2) ∧
    Real.sqrt (2*paperDelta r s-paperDelta r s^2) ≤ Real.sqrt (2*paperDelta r s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
