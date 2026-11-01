-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_explicit_qutrit_clifford_circuit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.explicit_qutrit_clifford_circuit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:49:04.265602+00:00
-- url     : https://prove2.me/theorems/6c034084-6a63-42b6-9936-32824a0c0f2a
-- title:
--   The explicit two-adder qutrit Clifford circuit
-- statement:
--   For $x_1,x_2\in\mathbb Z_3$, first add the first wire into the second, then add the resulting second wire into the first. The resulting unitary is
--
--   $$U\lvert x_1,x_2\rangle=\lvert2x_1+x_2,x_1+x_2\rangle.$$
--
--   It normalizes the phase-aware two-qutrit Pauli group, hence is a Clifford unitary. For the four-qutrit state $\Psi$ defined by the nine terms in Appendix A.2, its precise tensor interpretation is
--
--   $$U_{y,x}=3\Psi(x_2,y_2,y_1,x_1).$$
--
--   Thus the input tensor legs are $(3,0)$ and output legs are $(2,1)$, using zero-based leg labels. This links the explicit circuit to the source tensor rather than to an unspecified flattening.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 46, Appendix A.2: explicit qutrit Clifford circuit (A.11)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.46, (A.11): the two opposite adders implement the explicit
Clifford flattening. Inputs are tensor legs (3,0); outputs are (2,1),
so the equality is linked to the nine coefficients on PDF p.45. -/
theorem explicit_qutrit_clifford_circuit :
    qutritCircuit = addUp * addDown ∧ IsQutritClifford qutritCircuit ∧
    (∀ x y : Fin 2 → Trit,
      qutritCircuit y x = 3 * fourQutritState ![x 1, y 1, y 0, x 0]) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
