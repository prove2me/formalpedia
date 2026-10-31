-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_max_support_entropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.max_support_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:02:17.121387+00:00
-- url     : https://prove2.me/theorems/ffd1401f-06f9-482e-a786-017aed74bfa9
-- title:
--   §6.1.3 (6.22)–(6.23): max-entropy versus support entropy
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For every subnormalized rho_AB, including zero, the max-entropy is at most the optimized logarithmic support trace. This support entropy equals the logarithm of the operator norm of the partial trace of the support projector; the scalar reference-state maximum is attained.
--
--   $$
--   H_{\max}(A|B)_\rho\le H_0^\uparrow(A|B)_\rho=\log_2\|\operatorname{Tr}_A\{\rho>0\}\|_\infty.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 95, §6.1.3 (6.22)–(6.23): max-entropy versus support entropy

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

/-- NODE paper:1504.00233#6.hartleybound
§6.1.3 (6.22)–(6.23): max-entropy versus support entropy, arXiv:1504.00233v5, PDF p.95,96. -/
theorem max_support_entropy [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : paperSubnormalized r) :
    hmax r ≤ hartleyConditional r ∧ hartleyConditional r = paperLogE ‖traceLeft (paperPower r 0)‖ ∧
    (∃ s : paperMat B, paperSubnormalized s ∧ (paperPower r 0*Matrix.kronecker (1:paperMat A) s).trace.re = ‖traceLeft (paperPower r 0)‖) ∧
    (∀ s : paperMat B, paperSubnormalized s → (paperPower r 0*Matrix.kronecker (1:paperMat A) s).trace.re ≤ ‖traceLeft (paperPower r 0)‖) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
