-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_fully_quantum_aep
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.fully_quantum_aep
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:58:05.463144+00:00
-- url     : https://prove2.me/theorems/1e43ec5d-ad4d-4342-b8ba-f37609558e39
-- title:
--   Fully quantum asymptotic equipartition property
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For every normalized finite-dimensional bipartite state and every fixed 0<ε<1, both (1/n)Hmin^ε(A^n|B^n) and (1/n)Hmax^ε(A^n|B^n) of ρ_AB^⊗n converge to H(A|B)_ρ.
--
--   $$
--   \lim_{n\to\infty}\frac1n H_{\min}^{\varepsilon}(A^n|B^n)_{\rho^{\otimes n}}=H(A|B)_\rho=\lim_{n\to\infty}\frac1n H_{\max}^{\varepsilon}(A^n|B^n)_{\rho^{\otimes n}}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 91, seed

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

/-- NODE paper:1504.00233
seed, arXiv:1504.00233v5, PDF p.1,91,105,109,110,111. -/
theorem fully_quantum_aep [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    Tendsto (minRate r e) atTop (nhds (conditionalVN r:EReal)) ∧
    Tendsto (maxRate r e) atTop (nhds (conditionalVN r:EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
