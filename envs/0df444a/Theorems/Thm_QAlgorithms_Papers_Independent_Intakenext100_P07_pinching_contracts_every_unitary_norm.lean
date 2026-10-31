-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_pinching_contracts_every_unitary_norm
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.pinching_contracts_every_unitary_norm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:40:24.118667+00:00
-- url     : https://prove2.me/theorems/9bd19528-6e86-460a-a50f-f3dc0e1dcd10
-- title:
--   §3.1.1 (3.4): pinching contracts unitarily invariant norms
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   Every pinching channel contracts every unitarily invariant norm on finite operators, not only the operator norm or one Schatten norm.
--
--   $$
--   \left|\!\left|\!\left|\sum_xP_xLP_x\right|\!\right|\!\right|\le|||L|||.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 40, §3.1.1 (3.4): pinching contracts unitarily invariant norms

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

/-- NODE paper:1504.00233#3.pinchingnorm
§3.1.1 (3.4): pinching contracts unitarily invariant norms, arXiv:1504.00233v5, PDF p.40. -/
theorem pinching_contracts_every_unitary_norm [Nonempty I] {m : ℕ} (hm : 0 < m) (P : Fin m → paperMat I)
    (hP : Resolution P) (v : paperMat I → ℝ) (hv : UnitaryInvariantNorm v) (M : paperMat I) :
    v (resolutionPinch P M) ≤ v M := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
