-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_qubitObservables
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.qubitObservables
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:27:56.169582+00:00
-- url     : https://prove2.me/theorems/e21f4809-2180-4321-998b-fa91266c7f91
-- title:
--   Section IV A: d^2 observable averages for n qubits
-- statement:
--   For $n\ge0$ qubits, put $d=2^n$. Let $\mathcal E$ be CPTP and $U$ unitary. Index Pauli products $P_j$ and input states $\rho_k$ by strings in $\{0,1,2,3\}^n$, where each input factor is $I/2,(I+X)/2,(I+Y)/2$, or $(I+Z)/2$. Expand $P_j=\sum_k a_{jk}\rho_k$ using the real tensor-product coefficients from $I=2\rho_0$ and $P=2\rho_P-2\rho_0$. Define $\sigma_k=\sum_j a_{jk}UP_j^\dagger U^\dagger$. Every $\rho_k$ is normalized and every $\sigma_k$ is Hermitian, and
--
--   $$F_{\rm pro}(\mathcal E,U)=d^{-3}\sum_k\operatorname{tr}(\sigma_k\mathcal E(\rho_k)),\qquad |\{0,1,2,3\}^n|=d^2.$$
--
--   Thus $d^2$ observable averages suffice. The source's one-qubit input matrices are normalized here and their coefficients recomputed accordingly.
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 7, Section IV A: d^2 observable averages for n qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section IV A, PDF pp.6--7: d^2 Hermitian averages for n qubits.
PRINTED inputs I,I+X,I+Y,I+Z have trace two. CHANGED: divide each factor by two;
productCoefficient is recomputed in that normalized basis. Zero qubits is permitted. -/
theorem qubitObservables (n : ℕ) (E : FiniteProcess (Qubits n) (Qubits n))
    (U : Matrix.unitaryGroup (Qubits n) ℂ) :
    (∀ k, IsDensityMatrix (tomographyProductInput n k) ∧ (productObservable n U k).IsHermitian) ∧
    (∀ j, productPauli n j = ∑ k : Fin n → Fin 4,
      (productCoefficient n j k : ℂ) • tomographyProductInput n k) ∧
    proFidelity E.val (conjSuperop (U : Matrix (Qubits n) (Qubits n) ℂ)) =
      (2 ^ n : ℝ)⁻¹ ^ 3 * ∑ k : Fin n → Fin 4,
        effectProb (productObservable n U k) (E.val (tomographyProductInput n k)) ∧
    Fintype.card (Fin n → Fin 4) = (2 ^ n) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
