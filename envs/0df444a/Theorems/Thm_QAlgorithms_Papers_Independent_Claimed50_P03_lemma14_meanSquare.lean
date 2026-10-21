-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma14_meanSquare
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma14_meanSquare
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:57:58.663003+00:00
-- url     : https://prove2.me/theorems/4abf9a5b-81c9-420e-8a49-eefbccbd7f3e
-- title:
--   Lemma 14 (Mean squared error)
-- statement:
--   Let $\mathcal D$ be a Borel probability law on normalized $n$-qubit density matrices, invariant under Hadamard and phase gates on each wire independently. Discrete and entangled-state laws are allowed. For a subsystem $S$, define $\gamma^*(\rho_S)=2^{-|S|}\sum_{Q\in\{X,Y,Z\}^{\otimes S}}\operatorname{tr}(Q\rho_S)^2$, with $\gamma^*(\rho_\varnothing)=1$. For a phase-free Pauli $P$, write $\beta_{\mathcal D}(P)=(2/3)^{|P|}\mathbb E_{\mathcal D}\gamma^*(\rho_{\operatorname{supp}P})$.
--
--   For Hermitian $O_1,O_2$, let $\Delta\alpha_P=2^{-n}\operatorname{tr}(P(O_1-O_2))$. Then
--   $$\mathbb E_{\rho\sim\mathcal D}|\operatorname{tr}(O_1\rho)-\operatorname{tr}(O_2\rho)|^2=\sum_P\beta_{\mathcal D}(P)|\Delta\alpha_P|^2.$$
--   This diagonalizes mean squared prediction error in Pauli coefficients, including the identity.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 36, Lemma 14 (Mean squared error)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 14, paper p.36, D6: identity included, with empty-subsystem purity one. -/
theorem lemma14_meanSquare (n : ℕ) (O1 O2 : (Matrix (Qubits n) (Qubits n) ℂ))
    (h1 : O1.IsHermitian) (h2 : O2.IsHermitian)
    (D : Measure ((Matrix (Qubits n) (Qubits n) ℂ))) (hD : IsStateLaw D) (hflat : IsLocallyFlat D) :
    (∫ rho, |effectProb O1 rho - effectProb O2 rho| ^ 2 ∂D) = coefficientRisk D O1 O2 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
