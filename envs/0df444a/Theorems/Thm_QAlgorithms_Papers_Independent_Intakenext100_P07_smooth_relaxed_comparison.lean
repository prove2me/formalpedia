-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_relaxed_comparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_relaxed_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:54:26.46298+00:00
-- url     : https://prove2.me/theorems/255248c6-acf9-460b-8bbd-21b9b4bc5726
-- title:
--   §6.4.2 (6.107): relaxed smooth min/max comparison
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   Let rho_AB be normalized, let epsilon and delta be strictly positive with epsilon+delta<1, and let n>=1. The displayed comparison holds for the actual iid product state; interchanging the two radii gives its symmetric counterpart.
--
--   $$
--   \frac1n H_{\min}^{\varepsilon}(A^n|B^n)\le\frac1n H_{\max}^{\delta}(A^n|B^n)+\frac1n\log_2\frac1{1-(\varepsilon+\delta)^2}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 110, §6.4.2 (6.107): relaxed smooth min/max comparison

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

/-- NODE paper:1504.00233#6.relaxedcomparison
§6.4.2 (6.107): relaxed smooth min/max comparison, arXiv:1504.00233v5, PDF p.110. -/
theorem smooth_relaxed_comparison [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (e d : ℝ) (he : 0 < e) (hd : 0 < d) (hed : e+d < 1) (n : ℕ) (hn : 0 < n) :
    minRate r e n ≤ maxRate r d n+((Real.logb 2 (1/(1-(e+d)^2))/(n:ℝ):ℝ):EReal) ∧
    minRate r d n ≤ maxRate r e n+((Real.logb 2 (1/(1-(e+d)^2))/(n:ℝ):ℝ):EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
