-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_real_input_perfect_not
-- name    : QAlgorithms.Papers.Independent.Support21.P18.real_input_perfect_not
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:54:03.280089+00:00
-- url     : https://prove2.me/theorems/d5c68227-724c-492f-a0d1-835a98e60be4
-- title:
--   A fixed perfect NOT for real-amplitude qubits
-- statement:
--   In the specified computational basis let $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. It is unitary, and $\rho\mapsto J\rho J^\dagger$ is a CPTP gate. For every unit vector $\psi=\alpha|0\rangle+\beta|1\rangle$ with $\alpha,\beta\in\mathbb R$,
--   $$
--   J\psi=\psi^\perp,\qquad
--   J|\psi\rangle\langle\psi|J^\dagger=I-|\psi\rangle\langle\psi|,
--   \qquad F=1,
--   $$
--   where $\psi^\perp=\overline\beta|0\rangle-\overline\alpha|1\rangle$ and $F$ is the overlap with the orthogonal complement density.
--
--   The single fixed gate acts perfectly on this known great circle, and therefore on every pure ray with such a real representative.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 4, Role of a priori knowledge: exact NOT on real-amplitude qubit states

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.1-2,4, real-input exception: a single fixed physical unitary realizes
perfect complementation on the specified real great circle of pure qubit rays. -/
theorem real_input_perfect_not :
    realNotMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    IsChannel (conjSuperop realNotMatrix) ∧
    ∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi → HasRealCoordinates psi →
      act realNotMatrix psi = theta psi ∧
      conjSuperop realNotMatrix (pureDensity psi) = orthogonalDensity psi ∧
      effectProb (orthogonalDensity psi) (conjSuperop realNotMatrix (pureDensity psi)) = 1 := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
