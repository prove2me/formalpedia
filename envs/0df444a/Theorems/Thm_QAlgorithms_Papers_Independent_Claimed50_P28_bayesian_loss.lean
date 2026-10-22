-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_bayesian_loss
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.bayesian_loss
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:15:00.526974+00:00
-- url     : https://prove2.me/theorems/1ac3cfdd-d680-4d78-aac1-c586cda9c0d1
-- title:
--   General Bayesian loss and projected representation
-- statement:
--   Consider a probability ensemble $R_k$ of density matrices with a POVM, or of output-first Choi matrices of completely positive trace-nonincreasing operations with a physical tester. Let $\Pi_x$ denote the measurement/tester density and $\Delta_x$ a linear reconstruction dual on a complex subspace $V$ containing the prior support. Let $G\succeq0$ describe the representation, for example $G=\sum_n q_n|A_n\rangle\!\rangle\langle\!\langle A_n|$ with $q_n>0$. Put $\bar R=\int R_k\,d\nu(k)$ and $q_G(A)=\langle\!\langle A|G|A\rangle\!\rangle$. If the relevant integrands are integrable, then
--
--   $$\int\delta_{R_k,G}\,d\nu(k)=\int q_G(\Delta_x)\operatorname{Tr}(\bar R\Pi_x)\,d\mu(x)-\int q_G(R_k)\,d\nu(k).$$
--
--   Here $\delta_{R,G}$ is the estimator second moment minus $q_G(R)$. If $Q$ is the orthogonal projector onto $V$, the projected representation replaces $G$ by $QGQ$ in the first term, while the ensemble-only second term is unchanged. Also $\operatorname{Tr}(R_kQA)=\operatorname{Tr}(R_kA)$, where $QA$ denotes operator-space action. Only the first term depends on the setup and dual. Missing probability for trace-decreasing operations is a failure outcome with estimator zero, without conditional renormalization.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 1, (8)–(10); p.2 (19)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF pp.1–2, (8)–(10),(19)–(20): arbitrary-prior Bayesian loss and subspace reduction.
The state and operation cases are kept as two physical alternatives. Projection changes the
estimator to the projected representation; it need not preserve an arbitrary unprojected dual's noise. -/
theorem bayesian_loss {di do_ : ℕ} (hi : 0 < di) (ho : 0 < do_)
    {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]
    (mu : Measure X) (nu : Measure K) [SFinite mu] [IsProbabilityMeasure nu]
    (P D : X → Op (Fin do_ × Fin di)) (R : K → Op (Fin do_ × Fin di))
    (V : Set (Op (Fin do_ × Fin di))) (G Q : HSMatrix (Fin do_ × Fin di))
    (hphysical : ((∀ k, QAlgorithms.IsDensityMatrix (R k)) ∧ IsPOVMDensity mu P) ∨
      ((∀ k, IsOperation (R k)) ∧ IsTesterDensity mu P))
    (hdual : IsTomographyDual mu P D V) (hsupport : ∀ k, R k ∈ V)
    (hG : G.PosSemidef) (hQ : Qᴴ = Q ∧ Q * Q = Q)
    (hQV : ∀ A, A ∈ V ↔ onOperator Q A = A)
    (hint : BayesianIntegrable mu nu P D R G)
    (hintQ : BayesianIntegrable mu nu P D R (Q * G * Q)) :
    BayesianReduction mu nu P D R G Q ∧
    (∀ k A, (R k * onOperator Q A).trace = (R k * A).trace) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
