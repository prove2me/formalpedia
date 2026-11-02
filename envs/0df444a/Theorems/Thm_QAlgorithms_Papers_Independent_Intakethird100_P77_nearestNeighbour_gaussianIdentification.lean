-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_nearestNeighbour_gaussianIdentification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.nearestNeighbour_gaussianIdentification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:14:06.332337+00:00
-- url     : https://prove2.me/theorems/39a0ee8d-aa97-4c50-b458-5f866ce2d2c1
-- title:
--   Adjacent Gaussian gates are exactly special-unitary parity blocks, with common phases separated
-- statement:
--   Fix an existing adjacent pair of wires in increasing order in the Jordan–Wigner representation. Let $\mathcal G$ be the set of operators $e^{iH}$, with $H=i\sum_{\mu\ne\nu}h_{\mu\nu}c_\mu c_\nu$, real antisymmetric $h$, and all coefficients outside the four Majoranas of that pair equal to zero. Then
--
--   $$\mathcal G=\{G(A,B):A,B\in SU(2)\},\qquad \{G(A,B):A,B\in U(2),\det A=\det B\}=\{zV:|z|=1,\ V\in\mathcal G\}.$$
--
--   All operators are embedded on the specified pair and act as identity elsewhere. The two parity bases are ordered $00,11$ and $01,10$. This gives the exact local identification while retaining the scalar phase needed for general allowable matchgates.
--
--   **Source correction.** The unrestricted equal-determinant assertion on p.11 omits the common scalar phase; the trace-free quadratics themselves generate determinant-one blocks.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 11, Section 5: local Gaussian gates and nearest-neighbour matchgates, with phase correction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.10--11 local identification, with the scalar-phase omission
corrected: trace-free quadratics give exactly determinant-one parity blocks;
general equal-determinant blocks are these times a common unit scalar. -/
theorem nearestNeighbour_gaussianIdentification {n : ℕ} (w : Fin 2 ↪ Fin n)
    (hadjacent : (w 0).val + 1 = (w 1).val) (U : Op (Qubits n)) :
    ((∃ h : Matrix (Major n) (Major n) ℝ,
        Skew h ∧ SupportedOnPair w h ∧ U = gaussianOperation (jordanWigner n) h) ↔
      ∃ A B : Matrix.unitaryGroup Bool ℂ,
        Matrix.det (A : Matrix Bool Bool ℂ) = 1 ∧
        Matrix.det (B : Matrix Bool Bool ℂ) = 1 ∧
        U = embedOp (parityGate A B) w) ∧
    ((∃ A B : Matrix.unitaryGroup Bool ℂ,
        Matrix.det (A : Matrix Bool Bool ℂ) = Matrix.det (B : Matrix Bool Bool ℂ) ∧
        U = embedOp (parityGate A B) w) ↔
      ∃ (z : ℂ) (h : Matrix (Major n) (Major n) ℝ),
        ‖z‖ = 1 ∧ Skew h ∧ SupportedOnPair w h ∧
        U = z • gaussianOperation (jordanWigner n) h) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
