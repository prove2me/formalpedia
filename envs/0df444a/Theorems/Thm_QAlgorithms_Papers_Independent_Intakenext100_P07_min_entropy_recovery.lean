-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_min_entropy_recovery
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.min_entropy_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:49:47.791447+00:00
-- url     : https://prove2.me/theorems/d0fce399-aa49-4fdb-9150-cff2fda7773c
-- title:
--   §6.1.2 (6.9)–(6.11): entanglement interpretations of min-entropy
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$.
--
--   exp(−Hmin)=d_A max_E Tr[E_B→Aprime(ρ_AB)ψ_AAprime]. On normalized centers this is squared-fidelity recovery with lower bound −log d_A; the dual dimension-swapped formula (6.11) gives lower bound −log d_B.
--
--   $$
--   2^{-H_{\min}(A|B)_\rho}=d_A\max_{\mathcal E:B\to A^\prime}\operatorname{Tr}((\mathrm{id}_A\otimes\mathcal E)(\rho)\psi_{AA^\prime})=d_B\max_{\mathcal E:B^\prime\to A}\operatorname{Tr}(\rho(\mathcal E\otimes\mathrm{id}_B)(\psi_{B^\prime B})).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 93, §6.1.2 (6.9)–(6.11): entanglement interpretations of min-entropy

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

/-- NODE paper:1504.00233#6.operationalmin
§6.1.2 (6.9)–(6.11): entanglement interpretations of min-entropy, arXiv:1504.00233v5, PDF p.93,94. -/
theorem min_entropy_recovery [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : paperSubnormalized r) :
    (∃ E : paperMat B →ₗ[ℂ] paperMat A, paperCPTP E ∧
      ENNReal.ofReal ((Fintype.card A:ℝ)*(idTensorSuperop E r*paperEntangled A).trace.re) = expE (-paperHmin r) ∧
      (∀ F : paperMat B →ₗ[ℂ] paperMat A, paperCPTP F →
        (idTensorSuperop F r*paperEntangled A).trace.re ≤ (idTensorSuperop E r*paperEntangled A).trace.re) ∧
      (IsDensityMatrix r → paperHmin r = -paperLogE ((Fintype.card A:ℝ)*paperFidelity (idTensorSuperop E r) (paperEntangled A)))) ∧
    (∃ E : paperMat B →ₗ[ℂ] paperMat A, paperCPTP E ∧
      ENNReal.ofReal ((Fintype.card B:ℝ)*(r*preparedEntangled E).trace.re) = expE (-paperHmin r) ∧
      (∀ F : paperMat B →ₗ[ℂ] paperMat A, paperCPTP F → (r*preparedEntangled F).trace.re ≤ (r*preparedEntangled E).trace.re)) ∧
    (IsDensityMatrix r → (-Real.logb 2 (Fintype.card A):EReal) ≤ paperHmin r ∧
      (-Real.logb 2 (Fintype.card B):EReal) ≤ paperHmin r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
