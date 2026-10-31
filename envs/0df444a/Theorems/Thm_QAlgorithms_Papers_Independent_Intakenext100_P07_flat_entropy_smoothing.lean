-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_flat_entropy_smoothing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.flat_entropy_smoothing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:53:56.40527+00:00
-- url     : https://prove2.me/theorems/a254bea5-edcd-412c-a27f-6602669e6bc4
-- title:
--   §6.3.1 (6.58): exact smoothing of flat entropy
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For a normalized state rho with equal min- and max-entropy and 0 <= epsilon < 1, both smoothing optima are attained by t=(1-epsilon^2)rho. In bits,
--
--   $$
--   H_{\min}^{\varepsilon}(A|B)_\rho=H_{\min}(A|B)_\rho-\log_2(1-\varepsilon^2),\qquad H_{\max}^{\varepsilon}(A|B)_\rho=H_{\max}(A|B)_\rho+\log_2(1-\varepsilon^2).
--   $$
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 102, §6.3.1 (6.58): exact smoothing of flat entropy

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

/-- NODE paper:1504.00233#6.flatentropy
§6.3.1 (6.58) and its following max-entropy counterpart, PDF p.102.
Both optima are attained by the explicitly constructed (1-e^2)r. -/
theorem flat_entropy_smoothing [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (hf : paperHmin r = hmax r) (e : ℝ) (he : 0 ≤ e) (he1 : e < 1) :
    let t := ((1-e^2:ℝ):ℂ) • r
    t ∈ paperBall r e ∧ paperSmoothMin r e = paperHmin t ∧ paperSmoothMin r e = paperHmin r-(Real.logb 2 (1-e^2):EReal) ∧
    paperSmoothMax r e = hmax t ∧ paperSmoothMax r e = hmax r+(Real.logb 2 (1-e^2):EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
