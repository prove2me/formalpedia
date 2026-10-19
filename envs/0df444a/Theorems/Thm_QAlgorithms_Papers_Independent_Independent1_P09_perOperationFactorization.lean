-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_perOperationFactorization
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.perOperationFactorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:26:58.288215+00:00
-- url     : https://prove2.me/theorems/95cd1f01-9021-4a29-b4d9-a8650104973b
-- title:
--   Factorized cancellation and unbiased physical trials
-- statement:
--   Consider a fixed finite mitigation design on $n$ qubits. Its slots comprise a product preparation, an ordered list of inverse or compensation stages, and an observable measurement; every slot is used exactly once. At slot $j$, let $q_{j,i}$ be real coefficients, let $C_j=\sum_i|q_{j,i}|$, and set $C=\prod_jC_j$. Assume the ideal density matrix, ideal Hermitian observable and each ideal stage map equal the corresponding signed sums of their physical realizations, on every input operator. In an inverse stage the native map precedes the correction; compensation chooses either the native map or a basis branch.
--
--   Sample each choice with weight $|q_{j,i}|/C_j$, run the resulting physical circuit, and multiply the readout by the sign of the product of selected coefficients. A rejected postselection returns zero and remains a trial. If $Y$ is this effective outcome and $m$ is the ideal circuit expectation, then
--   $$\sum_\omega\Pr(\omega)=1,\qquad C\,\mathbb E[Y]=m,\qquad
--   \mathbb E\!\left[\frac C R\sum_{s=1}^R Y_s\right]=m\quad(R\ge1).$$
--   Here $Y_s$ are independent complete trials. If a slot has zero coefficient mass, the defined trial is a zero-scoring dummy; the decomposition then has zero target expectation. This states conditional factorization, rather than existence of a complete calibrated design.
--
--   **Correction to the printed source.**
--
--   Printed: PDF p.4 prints the preparation and output sampling probabilities as q/C, without absolute values.
--
--   Corrected: Use |q|/C for preparations and readouts as well as gate choices; negative coefficients remain encoded in the estimator sign.
--
--   Reason: The same paper's §IV p.4 and Appendix I.3 p.19 explicitly prescribe absolute weights. Signed q/C can be negative and is not a probability. Independent moderation is required.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §V (1), PDF p. 4. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P09

open ErrorMitigation











































/-- PDF p.4, §V (1): factorization and the actual sampled experiment.
Absolute sampling weights follow §IV and Appendix I, correcting §V's missing absolute signs. -/
theorem perOperationFactorization {n : ℕ} (D : MitigationDesign n)
    (rhoIdeal : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rhoIdeal)
    (Qideal : Matrix (Qubits n) (Qubits n) ℂ) (hQ : Qideal.IsHermitian)
    (ideal : Fin D.slots → Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ]
      Matrix (Qubits n) (Qubits n) ℂ)
    (hprep : rhoIdeal = ∑ i, (D.coefficient D.preparationSlot i : ℂ) • D.preparations i)
    (hout : Qideal = ∑ i, (D.coefficient D.observationSlot i : ℂ) • (D.observations i).observable)
    (hstage : ∀ stage ∈ D.stages, ∀ X,
      ideal stage.1 X = ∑ i, (D.coefficient stage.1 i : ℂ) •
        (instrumentWord (stageWord stage.2 i) X).1) :
    (∑ trial : Trial D, trialLaw D trial) = 1 ∧
    overhead D * (∑ trial : Trial D, trialLaw D trial * effectiveEstimator D trial) =
      (Qideal * D.stages.foldl (fun X stage => ideal stage.1 X) rhoIdeal).trace.re ∧
    ∀ R : ℕ, ∀ hR : 0 < R,
      (∑ trials : Fin R → Trial D, repeatedTrialLaw D R hR trials *
        reportedEstimator D R hR trials) =
          (Qideal * D.stages.foldl (fun X stage => ideal stage.1 X) rhoIdeal).trace.re := by sorry




















end QAlgorithms.Papers.Independent.Independent1.P09
