-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_quantum_guessing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.quantum_guessing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:51:08.368981+00:00
-- url     : https://prove2.me/theorems/278f245b-336a-4efd-b051-87b738d74072
-- title:
--   §6.1.4 (6.30)–(6.32): quantum guessing probability
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For CQ input blocks ρ_B(x), exp(−Hmin(X|B))=max_{POVM M}Σ_x Tr M_xρ_B(x), with an attaining POVM. The same measurement produces a classical Y for which Hmin(X|Y)=Hmin(X|B).
--
--   $$
--   2^{-H_{\min}(X|B)_\rho}=\max_{\{M_x\}\text{ POVM}}\sum_x\operatorname{Tr}(M_x\rho_B(x)),\qquad H_{\min}(X|Y)_{\mathcal M(\rho)}=H_{\min}(X|B)_\rho.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 97, §6.1.4 (6.30)–(6.32): quantum guessing probability

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

/-- NODE paper:1504.00233#6.guessing
§6.1.4 (6.30)–(6.32): quantum guessing probability, arXiv:1504.00233v5, PDF p.97. -/
theorem quantum_guessing [Nonempty X] [Nonempty B] (r : X → paperMat B)
    (hr : ∀ x, (r x).PosSemidef) (ht : (∑ x, (r x).trace.re) ≤ 1) :
    ∃ M : X → paperMat B, IsPOVM M ∧ ENNReal.ofReal (guessObjective r M) = expE (-paperHmin (paperCqState r)) ∧
      (∀ N : X → paperMat B, IsPOVM N → guessObjective r N ≤ guessObjective r M) ∧
      paperHmin (paperMeasuredJoint r M) = paperHmin (paperCqState r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
