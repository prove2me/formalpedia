-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_processLearner_runtime
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.processLearner_runtime
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:03:07.217244+00:00
-- url     : https://prove2.me/theorems/c49c6153-aa15-4100-8f6f-0d3c445d61ba
-- title:
--   Section III.A / Appendix E.1: full classical learning and prediction cost
-- statement:
--   Fix output locality $\kappa\ge1$ and participation $d\ge1$. Let $n,k,N\ge1$, $\widetilde\epsilon>0$, and let $O$ be supplied by a canonical nonzero sparse Pauli description with a $(\kappa,d)$ decomposition. Each training record consists of an input six-state product label and an output Pauli-measurement label. Set
--   $$L=\sum_{j=0}^{\min(k,n)}\binom nj3^j,\quad\eta=\sum_Q|a_Q|,\quad\widehat x_P=\frac1N\sum_\ell\operatorname{tr}(P\rho_\ell)y_\ell(O),\quad b_P=3^{-|P|}.$$
--   The implemented training loop enumerates all $|P|\le k$, computes the correlations using cached output labels, and applies the exact two-layer filter of Eq.(E16) with $\eta,\widetilde\epsilon,\widehat x_P,b_P$. Its prediction loop, given classical Pauli-moment access for a normalized test density matrix $\rho$, returns exactly
--   $$h(\rho,O)=\sum_{|P|\le k}\widehat\alpha_P\operatorname{tr}(P\rho).$$
--   There is $C_{\kappa,d}>0$, independent of $n,k,N,O,\rho$ and the records, such that the combined charged arithmetic/access cost is
--   $$T_{\rm training}+T_{\rm prediction}\le C_{\kappa,d}(nN+kNL+L),\qquad T_{\rm prediction}\le3L.$$
--   Collecting RDMs or moments from a quantum state is separate. This is the full classical learner cost; the $O(nN)$ output-label pass alone is not its training runtime.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 5, Section III.A / Appendix E.1: full classical learning and prediction cost

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Section III.A, paper p.5, and Appendix E.1, p.47: full classical E10-E17
training and prediction cost. Constants depend only on output locality and
participation; labels are cached in a random-access array. Input Pauli-moment
access is supplied classically; collecting RDMs is separate. -/
theorem processLearner_runtime :
    ∀ (kap d : ℕ), 1 ≤ kap → 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (n k N : ℕ), 1 ≤ n → 1 ≤ k → 1 ≤ N →
    ∀ (e : ℝ), 0 < e → ∀ terms : SparseObservable n,
      ValidDescription kap terms → HasBoundedDegree kap d (decodeObservable terms) →
      ∀ (data : Fin N → Shot n × Shot n) (rho : (Matrix (Qubits n) (Qubits n) ℂ)), IsDensityMatrix rho →
        let training := runProcessTraining k e terms data
        let prediction := runProcessPrediction training.value
          (fun w => effectProb (wordMatrix (decodeSparseWord w)) rho)
        prediction.value = processPredictor k e data (decodeObservable terms) rho ∧
        ((training.steps + prediction.steps : ℕ) : ℝ) ≤
          C * ((n : ℝ) * (N : ℝ) + (k : ℝ) * (N : ℝ) * (lowWeightPauliCount n k : ℝ) +
            (lowWeightPauliCount n k : ℝ)) ∧
        prediction.steps ≤ 3 * lowWeightPauliCount n k := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
