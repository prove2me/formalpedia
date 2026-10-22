-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_zero_stabilizer_unique
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.zero_stabilizer_unique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:40:00.89086+00:00
-- url     : https://prove2.me/theorems/a9a165c2-f630-4698-891c-8fd043adcced
-- title:
--   Fact 2: unique stabilizer coordinates of |0>
-- statement:
--   For real numbers $x,y,z$, put $M_{x,y,z}=xX+yY+zZ$, using the displayed Pauli matrices on page 10. If $M_{x,y,z}|0\rangle=|0\rangle$, then
--
--   $$x=0,\qquad y=0,\qquad z=1.$$
--
--   No prior assumption $x^2+y^2+z^2=1$ is made. Stabilization uses eigenvalue exactly $+1$. This identifies the stabilizer coordinates of the computational zero state.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 10, Fact 2: unique stabilizer coordinates of |0>

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.10, Fact 2 (proof p.11): a real tuple stabilizing |0>
with eigenvalue +1 must be (0,0,1); no unit-sphere premise is added. -/
theorem zero_stabilizer_unique (x y z : ℝ) (h : PauliStabilizes x y z (ket false)) :
    x = 0 ∧ y = 0 ∧ z = 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
