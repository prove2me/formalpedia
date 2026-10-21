-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma16_extract
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma16_extract
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:59:56.318802+00:00
-- url     : https://prove2.me/theorems/70f6b99d-169b-4101-8f12-a1a58eb4ee42
-- title:
--   Lemma 16 (Extracting Pauli coefficient)
-- statement:
--   Let $\mathcal D$ be a Borel probability law on normalized $n$-qubit density matrices, invariant under Hadamard and phase gates on each wire independently. Discrete and entangled-state laws are allowed. For a subsystem $S$, define $\gamma^*(\rho_S)=2^{-|S|}\sum_{Q\in\{X,Y,Z\}^{\otimes S}}\operatorname{tr}(Q\rho_S)^2$, with $\gamma^*(\rho_\varnothing)=1$. For a phase-free Pauli $P$, write $\beta_{\mathcal D}(P)=(2/3)^{|P|}\mathbb E_{\mathcal D}\gamma^*(\rho_{\operatorname{supp}P})$.
--
--   For Hermitian $O=\sum_Q\alpha_QQ$ and any phase-free $P$,
--   $$\mathbb E_{\rho\sim\mathcal D}[\operatorname{tr}(O\rho)\operatorname{tr}(P\rho)]=\alpha_P\beta_{\mathcal D}(P).$$
--   This coefficient-extraction identity includes the identity and does not divide by a weight that may vanish.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 37, Lemma 16 (Extracting Pauli coefficient)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 16, paper p.37, D16: coefficient extraction without dividing by
possibly zero subsystem purity; includes the identity word. -/
theorem lemma16_extract (n : ℕ) (O : (Matrix (Qubits n) (Qubits n) ℂ)) (hO : O.IsHermitian)
    (D : Measure ((Matrix (Qubits n) (Qubits n) ℂ))) (hD : IsStateLaw D) (hflat : IsLocallyFlat D)
    (P : (Fin n → Fin 4)) :
    (∫ rho, effectProb O rho * effectProb (wordMatrix P) rho ∂D) =
      coefficient O P * momentWeight D P := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
