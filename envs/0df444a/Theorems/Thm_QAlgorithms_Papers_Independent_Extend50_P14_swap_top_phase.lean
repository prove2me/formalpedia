-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_swap_top_phase
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.swap_top_phase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:02:43.975266+00:00
-- url     : https://prove2.me/theorems/1929028d-a5be-42ec-98c4-186d378d63ec
-- title:
--   The valid multi-register SWAP obstruction and catalyst
-- statement:
--   Let r≥1, let S swap two r-qubit registers, and let φ be real. With the 2r physical wires paired between registers,
--
--   $$\Phi_{2r}(e^{i\phi S})=2^r\phi\pmod{2\pi}.$$
--
--   If this angle is nonzero, e^{iφS} does not belong to V_k for any 1≤k<2r. Nevertheless a single ground-state ancillary qubit permits an exact coherent implementation using exchange interactions and ancilla Z, returning the ancilla for every input. No polynomial gate-count bound is claimed.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 6, II.F: the valid multi-register SWAP obstruction and catalyst

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.6: the valid top-body formula is 2^r phi, not 2r phi. The
nonzero-angle obstruction and an exact one-qubit catalyst are both retained. -/
theorem swap_top_phase (r : ℕ) (hr : 1 ≤ r) (phi : ℝ) :
    u1BodyPhase (schrodingerEvolution (multiSwap r) (-phi)) (2*r) = (((2 : ℝ)^r * phi : ℝ) : Real.Angle) ∧
    (∀ k : ℕ, 1 ≤ k → k < 2*r →
      (((2 : ℝ)^r * phi : ℝ) : Real.Angle) ≠ 0 →
      schrodingerEvolution (multiSwap r) (-phi) ∉ u1Group (2*r) k) ∧
    (∃ W : QMat (2*r+1), W ∈ controlGenerated (qubitCatalystControls (2*r)) ∧
      Catalyzes W (schrodingerEvolution (multiSwap r) (-phi))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
