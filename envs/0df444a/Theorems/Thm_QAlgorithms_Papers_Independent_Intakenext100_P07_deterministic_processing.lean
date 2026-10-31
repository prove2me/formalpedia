-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_deterministic_processing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.deterministic_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:29:26.612981+00:00
-- url     : https://prove2.me/theorems/33027a78-8d7f-4c44-8b3b-25a3d53fdcb8
-- title:
--   6.20
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For any deterministic f:X→Z on the classical register, both smooth entropies satisfy H^ε(ZA|B)_{f(ρ)}≤H^ε(XA|B)_ρ, with A retained and output blocks computed by summing preimages.
--
--   $$
--   H^\varepsilon(ZA|B)_\tau\le H^\varepsilon(XA|B)_\rho\quad(H=H_{\min},H_{\max}),\qquad Z=f(X).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 105, 6.20

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

/-- NODE paper:1504.00233#6.20
6.20, arXiv:1504.00233v5, PDF p.105. -/
theorem deterministic_processing [Nonempty X] [Nonempty Z] [Nonempty A] [Nonempty B] (r : paperMat ((X × A) × B))
    (hr : paperSubnormalized r) (hc : ClassicalLeft (paperRegroup r)) (f : X → Z) (e : ℝ) (he : Radius r e) :
    paperSmoothMin (classicalProcess f r) e ≤ paperSmoothMin r e ∧ paperSmoothMax (classicalProcess f r) e ≤ paperSmoothMax r e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
