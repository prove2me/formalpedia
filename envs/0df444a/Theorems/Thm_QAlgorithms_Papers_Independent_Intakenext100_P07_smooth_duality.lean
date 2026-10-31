-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_smooth_duality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.smooth_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:24:57.97638+00:00
-- url     : https://prove2.me/theorems/b4036999-8a50-4db9-8345-96c3dafa9331
-- title:
--   6.14
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For rank-one subnormalized ABC and 0≤ε<sqrt(Trρ), Hmax^ε(A|B)=−Hmin^ε(A|C).
--
--   $$
--   H_{\max}^{\varepsilon}(A|B)_\rho=-H_{\min}^{\varepsilon}(A|C)_\rho.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 101, 6.14

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

/-- NODE paper:1504.00233#6.14
6.14, arXiv:1504.00233v5, PDF p.101. -/
theorem smooth_duality [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : paperSubnormalized r) (hp : paperPure r) (e : ℝ) (he : Radius r e) :
    paperSmoothMax (traceRight r) e = -paperSmoothMin (paperTraceMiddle r) e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
