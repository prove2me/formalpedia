-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_normalized_min_optimizer
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.normalized_min_optimizer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:23:51.41746+00:00
-- url     : https://prove2.me/theorems/10bef3a7-eea2-44e0-8705-0a8a8e023b3d
-- title:
--   6.12
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For a normalized center and allowed radius, there exists an isometric enlargement of A and a normalized state in the enlarged ball attaining the original smooth min-entropy.
--
--   $$
--   \widehat\rho\in\mathcal B^\varepsilon(\rho_{A^\prime B}),\quad\operatorname{Tr}\widehat\rho=1,\quad H_{\min}(A^\prime|B)_{\widehat\rho}=H_{\min}^\varepsilon(A|B)_\rho.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 100, 6.12

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

/-- NODE paper:1504.00233#6.12
6.12, arXiv:1504.00233v5, PDF p.100. -/
theorem normalized_min_optimizer [Nonempty A] [Nonempty B] (r : paperMat (A × B))
    (hr : IsDensityMatrix r) (e : ℝ) (he : Radius r e) :
    ∃ n : ℕ, ∃ U : Matrix (Fin (n+1)) A ℂ, Uᴴ*U = 1 ∧ ∃ t : paperMat (Fin (n+1) × B),
      IsDensityMatrix t ∧ t ∈ paperBall (paperLocalEmbedding U (1:paperMat B) r) e ∧ paperHmin t = paperSmoothMin r e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
