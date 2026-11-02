-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P66_simultaneousReducedExplicit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P66.simultaneousReducedExplicit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:46:34.846715+00:00
-- url     : https://prove2.me/theorems/3b8df2bb-ccb3-4a38-88a0-f467c7d40a8e
-- title:
--   Explicit sufficient reduced-process sample counts
-- statement:
--   Let $n\ge1$, $0\le k\le n$ and $0<\epsilon,\delta<1$. Let $\rho=2^{-n}\Lambda_{\mathcal E}$ be the trace-one reference-first Choi state of any CPTP channel. For a $k$-element physical subsystem $S$, let $\rho_S$ retain both copies of $S$. Set $L_F=\log(2(8n)^{2k}/\delta)$, $L_1=\log((24n)^{2k}/\delta)$, and
--
--   $$
--   V_{\mathcal U}=\max_{S,P}\left\|\widetilde P_S-\frac{\operatorname{Tr}(\widetilde P_S)}{4^n}I\right\|_{\mathrm{shadow},\mathcal U}^2,
--   \qquad B_k=\max_P\|P\|_\infty^2=1.
--   $$
--
--   Here $P$ ranges over the $16^k$ phase-positive $2k$-qubit tensor Paulis and $\widetilde P_S$ extends $P$ by the identity to all $2n$ wires. For a fixed informationally complete measurement primitive $\mathcal U$, the following sufficient total counts are rounded upward:
--
--   $$
--   \begin{array}{ll}
--   \text{generic primitive, Frobenius:}&\left\lceil68\,4^k\epsilon^{-2}L_FV_{\mathcal U}\right\rceil,\\
--   \text{global Clifford, Frobenius:}&\left\lceil204\,4^{n+k}\epsilon^{-2}L_F\right\rceil,\\
--   \text{Pauli-6, Frobenius:}&\left\lceil68\,36^k\epsilon^{-2}L_FB_k\right\rceil,\\
--   \text{Pauli-6, trace:}&\left\lceil\frac83\,144^k\epsilon^{-2}L_1\right\rceil.
--   \end{array}
--   $$
--
--   For each clause, there exists an estimator independent of the channel, taking exactly the indicated number of independent fresh-shot records, for which
--
--   $$
--   \Pr[\forall S,\ \|\widehat\rho_S-\rho_S\|\le\epsilon]\ge1-\delta,
--   $$
--
--   using that clause's norm. The trace norm has no factor $1/2$. At $k=0$ return scalar $1$ without samples. The reduced channel has a maximally mixed complementary input; full tomography is $k=n$.
--
--   These explicit sufficient counts refine II.1. They are counts of all observations, not lengths of individual median-of-means batches. For the general Borel measurement primitive, the estimator is measurable, so the simultaneous success event is measurable.
-- source:
--   Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers, arXiv:2110.02965v3, PDF p. 14, Theorem A.3(i),(ii)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P66

noncomputable section

open MeasureTheory QAlgorithms ClassicalShadows

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P66

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Theorem A.3(i),(ii), PDF p.14, A5-A9. Ambient Pauli embeddings use 2n
wires and dimension 4^n; identity coefficients are exact. The estimator-line
O^(k) is corrected to O^(2k). Real sufficient prefactors are rounded upward
as total shots, not batch lengths. -/
theorem simultaneousReducedExplicit [∀ m : ℕ, Fintype (Clifford.ProjectiveGroup m)]
    (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (eps delta : ℝ)
    (heps : 0 < eps) (hepsOne : eps < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    (∀ P : MeasurementPrimitive (n + n), PrimitiveReducedRecovers P k
      (sampleCount k (68 * (4 : ℝ) ^ k / eps ^ 2 * reducedLog n k delta *
        reducedVariance P k)) eps delta) ∧
    ReducedRecovers (globalFrame (n + n)) k
      (sampleCount k (204 * (4 : ℝ) ^ (n + k) / eps ^ 2 * reducedLog n k delta))
      .frobenius eps delta ∧
    ReducedRecovers (pauliFrame (n + n)) k
      (sampleCount k (68 * (36 : ℝ) ^ k / eps ^ 2 * reducedLog n k delta *
        pauliNormEnvelope k)) .frobenius eps delta ∧
    ReducedRecovers (pauliFrame (n + n)) k
      (sampleCount k ((8 / 3 : ℝ) * (144 : ℝ) ^ k / eps ^ 2 * traceSampleLog n k delta))
      .trace eps delta := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P66

end
