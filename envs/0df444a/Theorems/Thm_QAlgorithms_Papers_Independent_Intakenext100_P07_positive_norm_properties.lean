-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_positive_norm_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.positive_norm_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:41:02.698803+00:00
-- url     : https://prove2.me/theorems/9122a2b6-5d53-4533-a789-9da478f2a7d9
-- title:
--   §3.1.2 (3.17)–(3.22): positive-cone dual norm
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$.
--
--   max_{0≤M≤I}|Tr ξM| is a complex operator norm; for self-adjoint ξ it is (Tr|ξ|+|Trξ|)/2; for ξ≥0 it equals Trξ. Include norm axioms and the absolute value.
--
--   $$
--   \|\xi\|_+=\max_{0\le M\le I}|\operatorname{Tr}(\xi M)|,\qquad\xi=\xi^\dagger\Longrightarrow\|\xi\|_+=\tfrac12(\|\xi\|_1+|\operatorname{Tr}\xi|).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 42, §3.1.2 (3.17)–(3.22): positive-cone dual norm

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

/-- NODE paper:1504.00233#3.positivenorm
§3.1.2 (3.17)–(3.22): positive-cone dual norm, arXiv:1504.00233v5, PDF p.42. -/
theorem positive_norm_properties [Nonempty I] :
    (∀ M : paperMat I, 0 ≤ positiveNorm M ∧ (positiveNorm M = 0 ↔ M = 0) ∧ positiveNorm M ≤ traceNorm M) ∧
    (∀ (z : ℂ) (M : paperMat I), positiveNorm (z • M) = ‖z‖*positiveNorm M) ∧
    (∀ M N : paperMat I, positiveNorm (M+N) ≤ positiveNorm M+positiveNorm N) ∧
    (∀ M : paperMat I, ∃ E : paperMat I, IsEffect E ∧ positiveNorm M = ‖(M*E).trace‖) ∧
    (∀ M : paperMat I, M.IsHermitian → positiveNorm M = (traceNorm M+‖M.trace‖)/2) ∧
    (∀ M : paperMat I, M.PosSemidef → positiveNorm M = traceNorm M ∧ positiveNorm M = M.trace.re) ∧
    (∀ M : paperMat I, ∀ v : I → ℂ, (∑ i, ‖v i‖^2) = 1 → ‖paperQuadratic M v‖ ≤ positiveNorm M) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
