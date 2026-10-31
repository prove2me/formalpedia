-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_generalizedFidelity_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.generalizedFidelity_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:01:44.237395+00:00
-- url     : https://prove2.me/theorems/c981febf-6f13-4d5d-96b9-126de1f671fd
-- title:
--   3.13
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   For subnormalized ρ,τ and any CPTNI E, F_*(Eρ,Eτ)≥F_*(ρ,τ).
--
--   $$
--   F_*(\mathcal E(\rho),\mathcal E(\tau))\ge F_*(\rho,\tau).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 46, 3.13

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

/-- NODE paper:1504.00233#3.13
3.13, arXiv:1504.00233v5, PDF p.46. -/
theorem generalizedFidelity_monotone [Nonempty I] [Nonempty J] (E : paperMat I →ₗ[ℂ] paperMat J) (hE : CPTNI E)
    (r s : paperMat I) (hr : paperSubnormalized r) (hs : paperSubnormalized s) :
    paperGeneralizedFidelity r s ≤ paperGeneralizedFidelity (E r) (E s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
