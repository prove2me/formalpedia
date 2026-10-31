-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_supported_optimizers
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.supported_optimizers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:22:27.492988+00:00
-- url     : https://prove2.me/theorems/a0bad932-8c6c-41be-8f24-f8390b11e2a0
-- title:
--   6.10
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   There are separate optimizers for smooth min and smooth max in the support of ρ_A⊗ρ_B; each is subnormalized and within radius ε.
--
--   $$
--   H_{\min}^{\varepsilon}(A|B)_\rho=H_{\min}(A|B)_{\widetilde\rho_{\min}},\qquad H_{\max}^{\varepsilon}(A|B)_\rho=H_{\max}(A|B)_{\widetilde\rho_{\max}},
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 99, 6.10

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

/-- NODE paper:1504.00233#6.10
6.10, arXiv:1504.00233v5, PDF p.99. -/
theorem supported_optimizers [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : paperSubnormalized r) (e : ℝ) (he : Radius r e) :
    (∃ t ∈ paperBall r e, paperSupported t (Matrix.kronecker (traceRight r) (traceLeft r)) ∧ paperSmoothMin r e = paperHmin t) ∧
    (∃ t ∈ paperBall r e, paperSupported t (Matrix.kronecker (traceRight r) (traceLeft r)) ∧ paperSmoothMax r e = hmax t) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
