-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_three_qubit_tomography
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.three_qubit_tomography
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:00:50.857384+00:00
-- url     : https://prove2.me/theorems/4346d68b-2ed1-48cb-a27b-637baa68731b
-- title:
--   Identifiability from the restricted three-qubit circuit
-- statement:
--   Let V,W be invariant three-qubit unitaries. For computational strings x,y and sites r,s with x_r=y_s=1, write x^- and y^- for the corresponding cleared-bit strings. The restricted circuit E8–E12 gives
--
--   $$q_V(x,y,r,s,\alpha)=\frac14\left|V_{y,x}+i e^{-2i\alpha}V_{y^-,x^-}\right|^2.$$
--
--   If q_V=q_W for every such input, output, pair of sites and real α, then W=e^{iβ}V for some real β. The output operations consist of ancilla exp(iαZ) and one exp(iπR_{s,a}/4), followed by computational measurement. This identifies the unknown unitary up to global phase.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 35, E.1: the restricted three-qubit tomography circuit

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.35–37, E8–E12: only the specified ancilla Z rotation and one
system/ancilla exchange are used in the output circuit. -/
theorem three_qubit_tomography (V W : QMat 3) (hV : U1Unitary V) (hW : U1Unitary W)
    (hData : ∀ (x y : Qubits 3) (r s : Fin 3) (alpha : ℝ), x r = true → y s = true →
      restrictedInterference V x y r s alpha = restrictedInterference W x y r s alpha) :
    ∃ alpha : ℝ, W = Complex.exp (Complex.I*alpha) • V := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
