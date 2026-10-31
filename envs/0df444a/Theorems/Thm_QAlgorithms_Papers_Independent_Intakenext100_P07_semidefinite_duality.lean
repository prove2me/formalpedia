-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_semidefinite_duality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.semidefinite_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:01:35.352004+00:00
-- url     : https://prove2.me/theorems/93c7c56b-746e-44b4-8e72-66ff94bbb3c3
-- title:
--   §6.1.1: weak duality and Slater strong duality
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   For the source SDP, primal extended infimum a≥dual extended supremum b; if a is finite and there exists a strictly positive dual variable Y with E†Y<K, then a=b and the primal infimum is attained.
--
--   $$
--   b\le a;\qquad a\in\mathbb R,\ \exists Y>0:\mathcal E^\dagger(Y)<K\Longrightarrow a=b=\operatorname{Tr}(KX_*)\text{ for a feasible }X_*.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 92, §6.1.1: weak duality and Slater strong duality

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

/-- NODE paper:1504.00233#6.sdpduality
§6.1.1: weak duality and Slater strong duality, arXiv:1504.00233v5, PDF p.92. -/
theorem semidefinite_duality [Nonempty I] [Nonempty J] (E : paperMat I →ₗ[ℂ] paperMat J) (K : paperMat I) (L : paperMat J)
    (hK : K.IsHermitian) (hL : L.IsHermitian) (hE : ∀ M : paperMat I, M.IsHermitian → (E M).IsHermitian) :
    sdpDual E K L ≤ sdpPrimal E K L ∧
    ((∃ a : ℝ, sdpPrimal E K L = (a:EReal)) →
      (∃ Y : paperMat J, Y.PosDef ∧ (K-paperAdjointAction E Y).PosDef) →
      sdpPrimal E K L = sdpDual E K L ∧ ∃ X : paperMat I, X.PosSemidef ∧ paperBelow L (E X) ∧
        ((K*X).trace.re:EReal) = sdpPrimal E K L) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
