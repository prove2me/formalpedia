-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_aep_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.aep_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:31:53.53299+00:00
-- url     : https://prove2.me/theorems/5899af12-5a3e-44d2-a93f-266388ad148c
-- title:
--   6.25
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For normalized ρ_AB and 0≤ε<1, the regularized smooth min-entropy limit is ≤H(A|B), and the regularized smooth max-entropy limit is ≥H(A|B). Include ε=0 without claiming equality at zero.
--
--   $$
--   \lim_n\frac1n H_{\min}^{\varepsilon}(A^n|B^n)\le H(A|B),\qquad\lim_n\frac1n H_{\max}^{\varepsilon}(A^n|B^n)\ge H(A|B).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 111, 6.25

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

/-- NODE paper:1504.00233#6.25
6.25, arXiv:1504.00233v5, PDF p.111. -/
theorem aep_converse [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1) :
    (∃ L : EReal, Tendsto (minRate r e) atTop (nhds L) ∧ L ≤ (conditionalVN r:EReal)) ∧
    (∃ L : EReal, Tendsto (maxRate r e) atTop (nhds L) ∧ (conditionalVN r:EReal) ≤ L) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
