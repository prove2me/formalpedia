-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma15_meanAbsolute
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma15_meanAbsolute
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:58:30.214889+00:00
-- url     : https://prove2.me/theorems/1907b5e5-3e3c-42ef-9f77-4335d0edc294
-- title:
--   Lemma 15 (Mean absolute error)
-- statement:
--   Let $\mathcal D$ be a Borel probability law on normalized $n$-qubit density matrices, invariant under Hadamard and phase gates on each wire independently. Discrete and entangled-state laws are allowed. For a subsystem $S$, define $\gamma^*(\rho_S)=2^{-|S|}\sum_{Q\in\{X,Y,Z\}^{\otimes S}}\operatorname{tr}(Q\rho_S)^2$, with $\gamma^*(\rho_\varnothing)=1$. For a phase-free Pauli $P$, write $\beta_{\mathcal D}(P)=(2/3)^{|P|}\mathbb E_{\mathcal D}\gamma^*(\rho_{\operatorname{supp}P})$.
--
--   For Hermitian $O_1,O_2$ and $\Delta\alpha_P=2^{-n}\operatorname{tr}(P(O_1-O_2))$,
--   $$\mathbb E_{\rho\sim\mathcal D}|\operatorname{tr}(O_1\rho)-\operatorname{tr}(O_2\rho)|\le\left(\sum_P\beta_{\mathcal D}(P)|\Delta\alpha_P|^2\right)^{1/2}.$$
--   This controls mean absolute prediction error by the same coefficient metric.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 36, Lemma 15 (Mean absolute error)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 15, paper p.36, D12: inequality for mean absolute error, not equality. -/
theorem lemma15_meanAbsolute (n : ℕ) (O1 O2 : (Matrix (Qubits n) (Qubits n) ℂ))
    (h1 : O1.IsHermitian) (h2 : O2.IsHermitian)
    (D : Measure ((Matrix (Qubits n) (Qubits n) ℂ))) (hD : IsStateLaw D) (hflat : IsLocallyFlat D) :
    (∫ rho, |effectProb O1 rho - effectProb O2 rho| ∂D) ≤ Real.sqrt (coefficientRisk D O1 O2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
