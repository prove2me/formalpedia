-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_pauli_conjugations
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.pauli_conjugations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:41:03.325484+00:00
-- url     : https://prove2.me/theorems/c43b4be2-dc90-4380-807d-3e3aa9f4ce77
-- title:
--   Section 4.2, Eqs.(10)–(12): exact Pauli conjugations
-- statement:
--   With the exact gates $H,P,T$ and Pauli matrices $X,Y,Z$ fixed as on pages 4 and 10, the following nine identities hold:
--
--   $$\begin{aligned}
--   HXH^\dagger&=Z,& HYH^\dagger&=-Y,& HZH^\dagger&=X,\\
--   PXP^\dagger&=Y,& PYP^\dagger&=-X,& PZP^\dagger&=Z,\\
--   TXT^\dagger&=(X+Y)/\sqrt2,& TYT^\dagger&=(Y-X)/\sqrt2,& TZT^\dagger&=Z.
--   \end{aligned}$$
--
--   The dagger is conjugate transpose. These are the exact supporting identities (10)–(12) for the stabilizer transitions.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 11, Section 4.2, Eqs.(10)–(12): exact Pauli conjugations

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.11, Eqs.(10)–(12): all nine exact Pauli conjugations. -/
theorem pauli_conjugations :
    hadamard * pauliX * star hadamard = pauliZ ∧
    hadamard * pauliY * star hadamard = -pauliY ∧
    hadamard * pauliZ * star hadamard = pauliX ∧
    phaseS * pauliX * star phaseS = pauliY ∧
    phaseS * pauliY * star phaseS = -pauliX ∧
    phaseS * pauliZ * star phaseS = pauliZ ∧
    gateT * pauliX * star gateT = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (pauliX + pauliY) ∧
    gateT * pauliY * star gateT = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (pauliY - pauliX) ∧
    gateT * pauliZ * star gateT = pauliZ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
